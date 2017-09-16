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
    flush: ArrayDeque<[LexerResult<'a>; 5]>,
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
            state:  ContractionState::NC,
            flush:  ArrayDeque::new(),
        }
    }
}

//============================================================================//
// Abbriviator, Internals:
//============================================================================//

impl<'a, I> LexerAbbreviator<'a, I>
where
    I: Iterator<Item = LexerResult<'a>>,
{
    fn readd_pop(&mut self) -> Option<LexerResult<'a>> {
        self.flush.extend(self.state.into_iter().map(|s| Ok(s)));
        self.flush.pop_front()
    }

    fn readd_pop_push(
        &mut self,
        push: LexerResult<'a>,
    ) -> Option<LexerResult<'a>> {
        match self.readd_pop() {
            None => Some(push),
            Some(retr) => {
                let p = self.flush.push_back(push);
                assert_eq!(p, None);
                Some(retr)
            }
        }
    }

    fn try_token(
        &mut self,
        tok: StrToken<'a>,
    ) -> (Option<LexerResult<'a>>, ContractionState) {
        #![allow(unreachable_patterns)]
        macro_rules! progress {
            ($newstate: expr, $emit: expr, $against: pat) => {
                match tok {
                    $against => ($emit, $newstate),
                    Const(Slash) => (self.readd_pop(), AA),
                    Axis(Parent) => (self.readd_pop(), BA),
                    Axis(SelfAxis) => (self.readd_pop(), CA),
                    Axis(Attribute) => (self.readd_pop_push(Ok(Const(AtSign))), NC),
                    _ => (self.readd_pop_push(Ok(tok)), NC)
                }
            };
        }
        macro_rules! second {
            ($newstate: expr, $against: pat, $init_state: expr, $init: pat) => {
                match tok {
                    $against => (None, $newstate),
                    $init => (self.readd_pop(), $init_state),
                    Const(Slash) => (self.readd_pop(), AA),
                    Axis(Parent) => (self.readd_pop(), BA),
                    Axis(SelfAxis) => (self.readd_pop(), CA),
                    Axis(Attribute) => (self.readd_pop_push(Ok(Const(AtSign))), NC),
                    _ => (self.readd_pop_push(Ok(tok)), NC)
                }
                /*
                if let $against = tok { (None, $newstate) }
                else if let $init = tok {
                    (self.readd_pop(), $init_state)
                }
                else { (self.readd_pop_push(Ok(tok)), NC) }
                        //if let $init = tok { $init_state } else { NC }) }
                */
            };
        }
        match self.state {
            NC => match tok {
                Const(Slash) => (None, AA),
                Axis(Parent) => (None, BA),
                Axis(SelfAxis) => (None, CA),
                Axis(Attribute) => (Some(Ok(Const(AtSign))), NC),
                _ => (Some(Ok(tok)), NC),
            },
            AA => second!(AB, Axis(DescendantOrSelf), AA, Const(Slash)),
            AB => progress!(AC, None, NType(Node)),
            AC => progress!(AD, None, Const(LeftParen)),
            AD => progress!(AE, None, Const(RightParen)),
            AE => progress!(NC, Some(Ok(Const(DoubleSlash))), Const(Slash)),
            BA => second!(BB, NType(Node), BA, Axis(Parent)),
            BB => progress!(BC, None, Const(LeftParen)),
            BC => progress!(NC, Some(Ok(Const(ParentNode))), Const(RightParen)),
            CA => second!(CB, NType(Node), CA, Axis(SelfAxis)),
            CB => progress!(CC, None, Const(LeftParen)),
            CC => progress!(NC, Some(Ok(Const(CurrentNode))), Const(RightParen)),
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
                let (emit, newstate) = match rtok {
                    Ok(tok) => self.try_token(tok),
                    err => (self.readd_pop_push(err), NC)
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
}

/// An iterator that contracts in reverse.
struct ContractionRevIter {
    state: ArrayVec<[StaticToken; 5]>,
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
                AD => trans_rev!(AC, Const(LeftParen)),
                AE => trans_rev!(AD, Const(RightParen)),
                // ParentNode transition chain:
                BA => trans_rev!(NC, Axis(Parent)),
                BB => trans_rev!(BA, NType(Node)),
                BC => trans_rev!(BB, Const(LeftParen)),
                // CurrentNode transition chain:
                CA => trans_rev!(NC, Axis(SelfAxis)),
                CB => trans_rev!(CA, NType(Node)),
                CC => trans_rev!(CB, Const(LeftParen)),
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
    use test;
    use std::mem::drop;
    use itertools::Itertools;
    use super::*;

    use lexer_deabbr::LexerDeabbreviator;

    mod prop_test {
        use super::*;
        use test_generators::*;

        proptest! {
            #[test]
            fn abbr_deabbr_identity(ref orig in gen_tokens()) {
                let tokens: Vec<LexerResult> =
                    orig.into_iter()
                        .map(Token::borrowed)
                        .filter(|x| *x != Axis(Attribute))
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
            (ad, AD) => [Const(Slash), Axis(DescendantOrSelf),
                         NType(Node), Const(LeftParen)],
            (ae, AE) => [Const(Slash), Axis(DescendantOrSelf),
                         NType(Node), Const(LeftParen), Const(RightParen)],
            // ParentNode transition chain:
            (ba, BA) => [Axis(Parent)],
            (bb, BB) => [Axis(Parent), NType(Node)],
            (bc, BC) => [Axis(Parent), NType(Node), Const(LeftParen)],
            // CurrentNode transition chain:
            (ca, CA) => [Axis(SelfAxis)],
            (cb, CB) => [Axis(SelfAxis), NType(Node)],
            (cc, CC) => [Axis(SelfAxis), NType(Node), Const(LeftParen)]
        }
    }
}
