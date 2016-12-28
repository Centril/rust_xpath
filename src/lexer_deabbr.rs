use super::lexer::*;

// tokens:
use super::tokens::*;
use super::tokens::CToken::*;
use super::tokens::AxisName::*;
use super::tokens::NodeType::*;
use super::tokens::Token::*;

//============================================================================//
// Deabbriviator:
//============================================================================//

#[derive(Clone, Copy)]
enum ExpansionState {
    // Finite State Machine(s):
    // Transitions: DA => DB => DC => None
    DA, DB, DC,
    // Transitions: NA => None
    NA
}

pub struct LexerDeabbreviator<I> {
    source: I,
    state:  Option<ExpansionState>
}

impl<I> LexerDeabbreviator<I> {
    pub fn new(source: I) -> LexerDeabbreviator<I> {
        LexerDeabbreviator {
            source: source,
            state:  None
        }
    }

    fn expand<'a>(&mut self, tok: Token<&'a str>) -> Token<&'a str> {
        use self::ExpansionState::*;
        match tok {
            Const(DoubleSlash) => {
                self.state = Some(DA);
                Const(Slash)
            },
            Const(CurrentNode) => {
                self.state = Some(NA);
                Axis(SelfAxis)
            },
            Const(ParentNode)  => {
                self.state = Some(NA);
                Axis(Parent)
            },
            Const(AtSign)      => Axis(Attribute),
            other              => other
        }
    }
}

impl<'a, I> Iterator for LexerDeabbreviator<I>
where I: Iterator<Item = LexResult<'a>> {
    type Item = LexResult<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        use self::ExpansionState::*;
        match self.state {
            None    => self.source.next().map(|x| x.map(|tok| self.expand(tok))),
            Some(p) => {
                let (ns, r) = match p {
                    NA => (None,     NType(Node)),
                    DA => (Some(DB), Axis(DescendantOrSelf)),
                    DB => (Some(DC), NType(Node)),
                    DC => (None,     Const(Slash)),
                };
                self.state = ns;
                Some(Ok(r))
            }
        }
    }
}

//============================================================================//
// Tests:
//============================================================================//

#[cfg(test)]
mod tests {
    use super::*;

    // helpers & macros:

    fn all_tokens(i: Vec<LexResult>) -> Vec<Token<&str>> {
        LexerDeabbreviator::new(i.into_iter())
            .collect::<Result<Vec<_>, LexerError>>().unwrap()
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

    use test;

    #[bench]
    fn bench_deabbr(b: &mut test::Bencher) {
        let x = "./..//Wikimedia/.././projects//project[@text='abc'][@name='Wikipedia']//editions//edition//text()";
        let l: Vec<LexResult> = Lexer::new(x).collect();
        b.iter(|| LexerDeabbreviator::new(l.clone().into_iter()).count());
    }

    // actual tests:

    tests! {
        (at_sign_to_attribute_axis, vec![Ok(Const(AtSign))])
            => vec![Axis(Attribute)],

        (double_slash_to_descendant_or_self, vec![Ok(Const(DoubleSlash))])
            => vec![Const(Slash), Axis(DescendantOrSelf),
                    NType(Node), Const(Slash)],

        (current_node_to_self_node, vec![Ok(Const(CurrentNode))])
            => vec![Axis(SelfAxis), NType(Node)],

        (parent_node_to_parent_node, vec![Ok(Const(ParentNode))])
            => vec![Axis(Parent), NType(Node)]
    }
}