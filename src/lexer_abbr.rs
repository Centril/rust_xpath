//============================================================================//
// Imports:
//============================================================================//

use arraydeque::ArrayDeque;
use arrayvec::ArrayVec;

use super::lexer::*;

use super::tokens::*;
use super::tokens::CToken::*;
use super::tokens::AxisName::*;
use super::tokens::NodeType::*;
use super::tokens::Token::*;

use self::ContractionState::*;

//============================================================================//
// Public API, Types:
//============================================================================//

/// `LexerAbbreviator` abbreviates the token stream from the lexer,
/// producing a larger token language, but with fewer tokens in total,
/// for the parser to deal with.
///
/// This is the reverse of `LexerAbbreviator`.
#[derive(Debug, Clone, PartialEq)]
pub struct LexerAbbreviator<'a, I>
where
    I: Iterator<Item = LexerResult<'a>>,
{
    /// The source token stream.
    source: I,
    /// Current contraction state.
    state: ContractionState,
    /// Failed contraction that must be immediately flushed out before
    /// anything else.
    flush: ArrayDeque<[LexerResult<'a>; 3]>,
}

//============================================================================//
// Public API, Implementation:
//============================================================================//

impl<'a, I> LexerAbbreviator<'a, I>
where
    I: Iterator<Item = LexerResult<'a>>,
{
    /// Constructs a new abbreviator.
    pub fn new(source: I) -> LexerAbbreviator<'a, I> {
        Self {
            source: source,
            state:  NC,
            flush:  ArrayDeque::new(),
        }
    }
}

//============================================================================//
// Abbriviator, Internals:
//============================================================================//

type OLR<'a> = Option<LexerResult<'a>>;

impl<'a, I> LexerAbbreviator<'a, I>
where
    I: Iterator<Item = LexerResult<'a>>,
{
    fn readd_pop(&mut self) -> OLR<'a> {
        // Not redundant, type checking does not working w/o the closure.
        #[cfg_attr(feature = "cargo-clippy", allow(redundant_closure))]
        self.flush.extend(self.state.into_iter().map(|s| Ok(s)));

        self.flush.pop_front()
    }

    fn readd_pop_push(&mut self, push: LexerResult<'a>) -> OLR<'a> {
        match self.readd_pop() {
            None => Some(push),
            Some(retr) => {
                let p = self.flush.push_back(push);
                assert_eq!(p, None);
                Some(retr)
            }
        }
    }

    fn try_token(&mut self, tok: StrToken<'a>) -> (ContractionState, OLR<'a>) {
        match self.state {
            NC => {},
            AA => if let Axis(DescendantOrSelf) = tok { return (AB, None); },
            AB => if let NType(Node) = tok { return (AC, None); }
            AC => if let Const(Slash) = tok {
                return (NC, Some(Ok(Const(DoubleSlash))));
            },
            BA => if let NType(Node) = tok {
                return (NC, Some(Ok(Const(ParentNode))));
            },
            CA => if let NType(Node) = tok {
                return (NC, Some(Ok(Const(CurrentNode))));
            },
        }
        match tok {
            Const(Slash) => (AA, self.readd_pop()),
            Axis(Parent) => (BA, self.readd_pop()),
            Axis(SelfAxis) => (CA, self.readd_pop()),
            Axis(Attribute) => (NC, self.readd_pop_push(Ok(Const(AtSign)))),
            _ => (NC, self.readd_pop_push(Ok(tok)))
        }
    }
}

impl<'a, I> Iterator for LexerAbbreviator<'a, I>
where
    I: Iterator<Item = LexerResult<'a>>,
{
    type Item = LexerResult<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        // Flush the left overs from a failed contraction if any:
        if let Some(ffront) = self.flush.pop_front() {
            return Some(ffront);
        }

        let mut emit_tok = None;
        while let None = emit_tok {
            if let Some(rtok) = self.source.next() {
                let (newstate, emit) = match rtok {
                    Ok(tok) => self.try_token(tok),
                    err => (NC, self.readd_pop_push(err))
                };
                emit_tok = emit;
                self.state = newstate;
            } else {
                let pop = self.readd_pop();
                self.state = NC;
                return pop;
            }
        }
        emit_tok
    }
}

//============================================================================//
// ContractionState, Internals:
//============================================================================//

type StaticToken = StrToken<'static>;

/// Tracks the state when abbreviating.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ContractionState {
    // Finite State Machine(s):
    /// Not contracting
    NC,
    /// Transitions: AA => AB => AC => NC
    AA,
    AB,
    AC,
    /// Transitions: BA => NC
    BA,
    /// Transitions: CA => NC
    CA,
}

/// An iterator that contracts in reverse.
struct ContractionRevIter {
    state: ArrayVec<[StaticToken; 3]>,
}

impl Iterator for ContractionRevIter {
    type Item = StaticToken;

    fn next(&mut self) -> Option<Self::Item> { self.state.pop() }
}

impl IntoIterator for ContractionState {
    type Item = StaticToken;
    type IntoIter = ContractionRevIter;

    fn into_iter(self) -> Self::IntoIter {
        let mut init = self;
        let mut state = ArrayVec::new();
        loop {
            macro_rules! trans_rev { ($newstate: expr, $tok: expr) => {{
                init = $newstate; state.push($tok);
            }}; }
            match init {
                // DoubleSlash transition chain:
                AA => trans_rev!(NC, Const(Slash)),
                AB => trans_rev!(AA, Axis(DescendantOrSelf)),
                AC => trans_rev!(AB, NType(Node)),
                // ParentNode transition chain:
                BA => trans_rev!(NC, Axis(Parent)),
                // CurrentNode transition chain:
                CA => trans_rev!(NC, Axis(SelfAxis)),
                // Not contracting
                NC => {
                    break;
                }
            }
        }
        ContractionRevIter { state }
    }
}

//============================================================================//
// Tests:
//============================================================================//

#[cfg(test)]
mod tests {
    use std::mem::drop;
    use itertools::Itertools;

    use super::*;
    use lexer_deabbr::LexerDeabbreviator;

    mod prop_test {
        use super::*;
        use test_generators::tokens::gen_tokens;

        proptest! {
            #[test]
            fn abbr_deabbr_identity(ref orig in gen_tokens()) {
                let tokens: Vec<LexerResult> =
                    orig.into_iter()
                        .map(Token::borrowed)
                        .filter(|x| *x != Axis(Attribute) &&
                                    *x != Axis(Parent) &&
                                    *x != Axis(SelfAxis))
                        .map(Ok)
                        .collect_vec();

                let adapt = LexerAbbreviator::new(LexerDeabbreviator::new(
                    (&tokens).into_iter().map(Clone::clone)
                )).collect_vec();

                assert_eq!(tokens, adapt);
            }

            #[test]
            fn deabbr_abbr_identity(ref orig in gen_tokens()) {
                let tokens: Vec<LexerResult> =
                    orig.into_iter()
                        .map(Token::borrowed)
                        .filter(|x| *x != Const(DoubleSlash) &&
                                    *x != Const(ParentNode)  &&
                                    *x != Const(CurrentNode) &&
                                    *x != Const(AtSign))
                        .map(Ok)
                        .collect_vec();

                let adapt = LexerDeabbreviator::new(LexerAbbreviator::new(
                    (&tokens).into_iter().map(Clone::clone)
                )).collect_vec();

                assert_eq!(tokens, adapt);
            }

            #[test]
            fn never_panic(ref orig in gen_tokens()) {
                let inner = orig.into_iter().map(Token::borrowed).map(Ok);
                LexerAbbreviator::new(inner).foreach(drop);
            }
        }
    }

    mod contraction_rev_iter {
        use super::*;

        macro_rules! tests {
            (($name: ident, $state: expr) => [$($elem:expr),*]) => {
                #[test]
                fn $name() {
                    assert_eq!($state.into_iter().collect_vec(),
                               vec![$($elem),*]);
                }
            };
            (($name: ident, $state: expr) => [$($elem:expr),*], $($args:tt)*) => {
                tests!(($name, $state) => [$($elem),*]);
                tests!($($args)*);
            };
        }

        tests! {
            (nc, NC) => [],
            // DoubleSlash transition chain:
            (aa, AA) => [Const(Slash)],
            (ab, AB) => [Const(Slash), Axis(DescendantOrSelf)],
            (ac, AC) => [Const(Slash), Axis(DescendantOrSelf), NType(Node)],
            // ParentNode transition chain:
            (ba, BA) => [Axis(Parent)],
            // CurrentNode transition chain:
            (ca, CA) => [Axis(SelfAxis)]
        }
    }
}
