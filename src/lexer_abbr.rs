//============================================================================//
// Imports:
//============================================================================//

use super::lexer::*;

use super::tokens::*;
use super::tokens::CToken::*;
use super::tokens::AxisName::*;
use super::tokens::NodeType::*;
use super::tokens::Token::*;

use std::mem;
use arraydeque::ArrayDeque;

//============================================================================//
// Public API, Types:
//============================================================================//

/// `LexerAbbreviator` abbreviates the token stream from the lexer,
/// producing a larger token language, but with fewer tokens in total,
/// for the parser to deal with.
///
/// This is the reverse of `LexerAbbreviator`.
/// The relation of these two iterators is:
/// + `LexerAbbreviator . LexerDeabbreviator = identity`
/// + `LexerDeabbreviator . LexerAbbreviator = identity`
#[derive(Debug, Clone, PartialEq)]
pub struct LexerAbbreviator<'a, I> {
    /// The source token stream.
    source: I,
    /// Current contraction state.
    state: ContractionState,
    /// Failed contraction that must be immediately flushed out before
    /// anything else.
    flush: BackStorage<LexerResult<'a>>,
}

//============================================================================//
// Public API, Implementation:
//============================================================================//

type BackStorage<T> = ArrayDeque<[T; 5]>;

impl<'a, I> LexerAbbreviator<'a, I> {
    /// Constructs a new abbreviator.
    pub fn new(source: I) -> LexerAbbreviator<'a, I> {
        Self {
            source: source,
            state:  ContractionState::NC,
            flush:  BackStorage::new(),
        }
    }
}

/// Tracks the state when abbreviating.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ContractionState {
    // Finite State Machine(s):
    /// Transitions: AA => AB => AC => AD => AE => NC
    AA,
    AB,
    AC,
    AD,
    AE,
    /// Transitions: BA, BB, BC => NC
    BA,
    BB,
    BC,
    /// Transitions: CA, CB, CC => NC
    CA,
    CB,
    CC,
    /// Not contracting
    NC,
}

/// An iterator that contracts in reverse.
struct ContractionRevIter {
    state: BackStorage<StrToken<'static>>,
}

impl Iterator for ContractionRevIter {
    type Item = StrToken<'static>;

    fn next(&mut self) -> Option<Self::Item> { self.state.pop_front() }
}

impl IntoIterator for ContractionState {
    type Item = StrToken<'static>;
    type IntoIter = ContractionRevIter;

    fn into_iter(self) -> Self::IntoIter {
        use self::ContractionState::*;
        let mut init = self;
        let mut state = ArrayDeque::new();
        {
            let mut trans_rev = |init: &mut ContractionState, nstate, tok| {
                *init = nstate;
                state.push_back(tok);
            };

            while init != NC {
                match init {
                    // DoubleSlash transition chain:
                    AA => trans_rev(&mut init, NC, Const(Slash)),
                    AB => trans_rev(&mut init, AA, Axis(DescendantOrSelf)),
                    AC => trans_rev(&mut init, AB, NType(Node)),
                    AD => trans_rev(&mut init, AC, Const(LeftParen)),
                    AE => trans_rev(&mut init, AD, Const(RightParen)),
                    // ParentNode transition chain:
                    BA => trans_rev(&mut init, NC, Axis(Parent)),
                    BB => trans_rev(&mut init, BA, NType(Node)),
                    BC => trans_rev(&mut init, BB, Const(LeftParen)),
                    // CurrentNode transition chain:
                    CA => trans_rev(&mut init, NC, Axis(SelfAxis)),
                    CB => trans_rev(&mut init, CA, NType(Node)),
                    CC => trans_rev(&mut init, CB, Const(LeftParen)),
                    // Not contracting
                    NC => {}
                }
            }
        }
        ContractionRevIter { state }
    }
}

impl<'a, I> LexerAbbreviator<'a, I> {
    fn readd_pop(&mut self) -> Option<LexerResult<'a>> {
        self.flush.extend(self.state.into_iter().map(|s| Ok(s)));
        self.flush.pop_front()
    }
}

impl<'a, I> Iterator for LexerAbbreviator<'a, I>
where
    I: Iterator<Item = LexerResult<'a>>,
{
    type Item = LexerResult<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        use self::ContractionState::*;
        // Flush the left overs from a failed contraction if any:
        if let Some(ffront) = self.flush.pop_front() {
            return Some(ffront);
        }

        // [Const(Slash), Axis(DecendantOrSelf), NType(Node), Const(LeftParen),
        // Const(RightParen)] match Const(Slash) => flush + emit DoubleSlash

        // [Const(Parent), NType(Node), Const(LeftParen)] + match
        // Const(RightParen) =>
        // flush + emit Const(ParentNode)

        // [Const(SelfAxis), NType(Node), Const(LeftParen)] + match
        // Const(RightParen) =>
        // flush + emit Const(CurrentNode)

        // match Axis(Attribute) => emit Const(AtSign)

        let mut emit_tok = None;
        let state = self.state;

        while let None = emit_tok {
            if let Some(rtok) = self.source.next() {
                let (emit, newstate) = match rtok {
                    Err(e) => {
                        let emit = self.readd_pop();
                        if emit.is_none() {
                            (Some(Err(e)), NC)
                        } else {
                            self.flush.push_back(Err(e));
                            (emit, NC)
                        }
                    }
                    Ok(tok) => {
                        match tok {
                            Axis(Attribute) => {
                                let emit = self.readd_pop();
                                if emit.is_none() {
                                    (Some(Ok(Const(AtSign))), NC)
                                } else {
                                    self.flush.push_back(Ok(Const(AtSign)));
                                    (emit, NC)
                                }
                            }
                            // DoubleSlash contraction:
                            Const(Slash) => match state {
                                AE => (Some(Ok(Const(DoubleSlash))), NC),
                                NC => (None, AA),
                                _ => (self.readd_pop(), AA),
                            },
                            Axis(DescendantOrSelf) => {
                                (None, if state == AA { AB } else { NC })
                            }
                            NType(Node) => match state {
                                AB => (None, AC),
                                BA => (None, BB),
                                CA => (None, CB),
                                _ => (self.readd_pop(), NC),
                            },
                            Const(LeftParen) => match state {
                                AC => (None, AD),
                                BB => (None, BC),
                                CB => (None, CC),
                                _ => (self.readd_pop(), NC),
                            },
                            Const(RightParen) => match state {
                                AD => (None, AE),
                                BC => (Some(Ok(Const(ParentNode))), NC),
                                CC => (Some(Ok(Const(CurrentNode))), NC),
                                _ => (self.readd_pop(), NC),
                            },
                            // ParentNode contraction:
                            Axis(Parent) => match state {
                                NC => (None, BA),
                                _ => (self.readd_pop(), BA),
                            },
                            // CurrentNode contraction:
                            Axis(SelfAxis) => match state {
                                NC => (None, CA),
                                _ => (self.readd_pop(), CA),
                            },
                            tok => (Some(Ok(tok)), NC),
                        }
                    }
                };
                emit_tok = emit;
                self.state = newstate;
            } else {
                return self.readd_pop();
            }
        }

        emit_tok
    }
}

/*  */

//============================================================================//
// Abbriviator, Internals:
//============================================================================//

/*
/// Tracks the state when abbreviating.
#[derive(Debug, Clone, PartialEq)]
struct ContractionState<'a> {
    tracker: [StrToken<'a>; 5],
}

impl<'a> ContractionState<'a> {
    fn new() -> Self {
        use std::mem;
        Self {
            // TODO: AUDIT unsafe!
            tracker: unsafe { mem::uninitialized() },
        }
    }
}


macro_rules! expand {
    ($self: expr, $next: expr, $yield: expr) => {
        { $self.state = $next; $yield }
    }
}

impl<I> LexerDeabbreviator<I> {
    fn expand<'a>(&mut self, tok: Token<&'a str>) -> Token<&'a str> {
        use self::ExpansionState::*;
        match tok {
            Const(DoubleSlash) => expand!(self, DA, Const(Slash)),
            Const(CurrentNode) => expand!(self, NA, Axis(SelfAxis)),
            Const(ParentNode) => expand!(self, NA, Axis(Parent)),
            Const(AtSign) => Axis(Attribute),
            other => other,
        }
    }
}

//============================================================================//
// Tests:
//============================================================================//

#[cfg(test)]
mod tests {
    use test;

    use super::*;
    use lexer::Error;

    // helpers & macros:

    fn all_tokens(i: Vec<LexerResult>) -> Vec<Token<&str>> {
        LexerDeabbreviator::new(i.into_iter())
            .collect::<Result<Vec<_>, Error>>()
            .unwrap()
    }

    macro_rules! tests {
        (($name: ident, $inp: expr) => $res: expr) => {
            #[test]
            fn $name() { assert_eq!(all_tokens($inp), {$res}); }
        };
        (($name: ident, $inp: expr) => $res: expr, $($args:tt)*) => {
            tests!(($name, $inp) => $res);
            tests!($($args)*);
        };
    }

    #[bench]
    fn bench_deabbr(b: &mut test::Bencher) {
        let x = concat!(
            "./..//Wikimedia/.././projects//project[@text='abc']",
            "[@name='Wikipedia']//editions//edition//text()"
        );
        let l: Vec<LexerResult> = Lexer::new(x).collect();
        b.iter(|| LexerDeabbreviator::new(l.clone().into_iter()).count());
    }

    // actual tests:
    tests! {
        (at_sign_to_attribute_axis, vec![Ok(Const(AtSign))])
            => vec![Axis(Attribute)],

        (double_slash_to_descendant_or_self, vec![Ok(Const(DoubleSlash))])
            => vec![Const(Slash), Axis(DescendantOrSelf),
                    NType(Node), Const(LeftParen), Const(RightParen),
                    Const(Slash)],

        (current_node_to_self_node, vec![Ok(Const(CurrentNode))])
            => vec![Axis(SelfAxis), NType(Node)],

        (parent_node_to_parent_node, vec![Ok(Const(ParentNode))])
            => vec![Axis(Parent), NType(Node)]
    }
}

*/
