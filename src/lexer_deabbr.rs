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
pub struct LexerDeabbreviator<I> {
    /// The source token stream.
    source: I,
    /// Current expansion state.
    state: ExpansionState,
}

//============================================================================//
// Public API, Implementation:
//============================================================================//

impl<I> LexerDeabbreviator<I> {
    /// Constructs a new deabbreviator.
    pub fn new(source: I) -> LexerDeabbreviator<I> {
        Self {
            source: source,
            state:  NE,
        }
    }
}

impl<S: AsRef<str>, E, I> Iterator for LexerDeabbreviator<I>
where
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
    /// Transitions: DA => DB => DC => DD => DE => NE
    DA,
    DB,
    DC,
    DD,
    DE,
    /// Transitions: NA => NE
    NA,
    NB,
    NC,
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
            NA => transition!(NB, NType(Node)),
            NB => transition!(NC, Const(LeftParen)),
            NC => transition!(NE, Const(RightParen)),
            // DA expansion FSM:
            DA => transition!(DB, Axis(DescendantOrSelf)),
            DB => transition!(DC, NType(Node)),
            DC => transition!(DD, Const(LeftParen)),
            DD => transition!(DE, Const(RightParen)),
            DE => transition!(NE, Const(Slash)),
        }
    }

    /// Start expanding if the given token warrants it and yield the first
    /// replacement token in the expansion chain.
    fn start_expand<S: AsRef<str>>(&mut self, tok: Token<S>) -> Token<S> {
        macro_rules! transition { ($newstate: expr, $ret: expr) => {{
            *self = $newstate; $ret
        }}; }
        match tok {
            Const(DoubleSlash) => transition!(DA, Const(Slash)),
            Const(CurrentNode) => transition!(NA, Axis(SelfAxis)),
            Const(ParentNode) => transition!(NA, Axis(Parent)),
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
    use lexer::{Error, Lexer, LexerResult};

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
            => vec![Axis(SelfAxis),
                    NType(Node), Const(LeftParen), Const(RightParen)],

        (parent_node_to_parent_node, vec![Ok(Const(ParentNode))])
            => vec![Axis(Parent),
                    NType(Node), Const(LeftParen), Const(RightParen)]
    }
}
