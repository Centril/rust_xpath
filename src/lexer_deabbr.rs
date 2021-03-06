//============================================================================//
// Imports:
//============================================================================//

use super::tokens::*;
use super::tokens::CToken::*;
use super::tokens::AxisName::*;
use super::tokens::NodeType::*;
use super::tokens::Token::*;

use self::ExpansionState::*;

//============================================================================//
// Public API, Types:
//============================================================================//

/// `LexerDeabbreviator` deabbreviates the token stream from the lexer,
/// producing a smaller token language for the parser to deal with.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LexerDeabbreviator<S, E, I>
where
    S: AsRef<str>,
    I: Iterator<Item = Result<Token<S>, E>>,
{
    /// The source token stream.
    source: I,
    /// Current expansion state.
    state: ExpansionState,
}

//============================================================================//
// Public API, Implementation:
//============================================================================//

impl<S, E, I> LexerDeabbreviator<S, E, I>
where
    S: AsRef<str>,
    I: Iterator<Item = Result<Token<S>, E>>,
{
    /// Constructs a new deabbreviator.
    pub fn new(source: I) -> LexerDeabbreviator<S, E, I> {
        Self {
            source: source,
            state:  NE,
        }
    }
}

impl<S, E, I> Iterator for LexerDeabbreviator<S, E, I>
where
    S: AsRef<str>,
    I: Iterator<Item = Result<Token<S>, E>>,
{
    type Item = Result<Token<S>, E>;

    fn next(&mut self) -> Option<Self::Item> {
        self.state.yield_expanded().map(Ok).or_else(|| {
            self.source
                .next()
                .map(|x| x.map(|tok| self.state.start_expand(tok)))
        })
    }
}

//============================================================================//
// ExpansionState, Internal FSM:
//============================================================================//

/// Tracks the state when deabbreviating.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ExpansionState {
    // Finite State Machine(s):
    /// Transitions: AA => AB => AC => NE
    AA,
    AB,
    AC,
    /// Transitions: BA => NE
    BA,
    /// Not expanding
    NE,
}

impl ExpansionState {
    /// Attempt to yield the next token from the current `ExpansionState`
    /// and advance the state to the next stage.
    fn yield_expanded<S: AsRef<str>>(&mut self) -> Option<Token<S>> {
        macro_rules! transition { ($newstate: expr, $ret: expr) => {{
            *self = $newstate; Some($ret)
        }}; }
        match *self {
            // No expansion state:
            NE => None,
            // NA expansion FSM:
            BA => transition!(NE, NType(Node)),
            // DA expansion FSM:
            AA => transition!(AB, Axis(DescendantOrSelf)),
            AB => transition!(AC, NType(Node)),
            AC => transition!(NE, Const(Slash)),
        }
    }

    /// Start expanding if the given token warrants it and yield the first
    /// replacement token in the expansion chain.
    fn start_expand<S: AsRef<str>>(&mut self, tok: Token<S>) -> Token<S> {
        macro_rules! transition { ($newstate: expr, $ret: expr) => {{
            *self = $newstate; $ret
        }}; }
        match tok {
            Const(DoubleSlash) => transition!(AA, Const(Slash)),
            Const(CurrentNode) => transition!(BA, Axis(SelfAxis)),
            Const(ParentNode) => transition!(BA, Axis(Parent)),
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

    use std::mem::drop;

    use itertools::Itertools;

    use lexer::{Lexer, LexerResult};

    use super::*;

    // helpers & macros:

    fn all_tokens<'a>(
        i: Vec<Result<StrToken<'a>, ()>>,
    ) -> Result<Vec<StrToken<'a>>, ()> {
        LexerDeabbreviator::new(i.into_iter()).collect()
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

    mod unit {
        use super::*;

        tests! {
            (err_to_err, vec![Err(())])
                => Err(()),

            (at_sign_to_attribute_axis, vec![Ok(Const(AtSign))])
                => Ok(vec![Axis(Attribute)]),

            (double_slash_to_descendant_or_self, vec![Ok(Const(DoubleSlash))])
                => Ok(vec![Const(Slash), Axis(DescendantOrSelf),
                           NType(Node), Const(Slash)]),

            (current_node_to_self_node, vec![Ok(Const(CurrentNode))])
                => Ok(vec![Axis(SelfAxis), NType(Node)]),

            (parent_node_to_parent_node, vec![Ok(Const(ParentNode))])
                => Ok(vec![Axis(Parent), NType(Node)])
        }
    }

    /// Tests with property based testing... using proptest:
    mod proptest {
        use super::*;
        use test_generators::tokens::gen_tokens;

        proptest! {
            #[test]
            fn never_panic(ref orig in gen_tokens()) {
                orig.into_iter().map(|t| t.borrowed()).map(Ok)
                    .foreach(|s: Result<StrToken, ()>| drop(s));
            }
        }
    }
}
