//============================================================================//
// Imports:
//============================================================================//

use std::borrow::Cow;

use proptest::prelude::*;
use proptest::char::CharStrategy;
use proptest::bool::weighted;
use proptest::strategy::{Union, ValueTree};
use proptest::test_runner::TestRunner;

use super::tokens::*;
use super::tokens::Token::*;
use super::tokens::CToken::*;
use super::tokens::AxisName::*;
use super::tokens::NodeType::*;

//============================================================================//
// Option(al):
//============================================================================//

pub fn optional<T: Strategy>(strat: T) -> OptionStrategy<T> {
    optional_weighted(strat, 0.5)
}

pub fn optional_weighted<T: Strategy>(strat: T, prob: f64) -> OptionStrategy<T> {
    OptionStrategy { strat, prob }
}

#[derive(Clone, Debug)]
pub struct OptionValueTree<T: ValueTree> {
    pick: Option<T>,
    prev: Option<T>,
}

#[derive(Clone, Debug)]
pub struct OptionStrategy<T: Strategy> {
    strat: T,
    prob: f64,
}

impl<T: Strategy> Strategy for OptionStrategy<T> {
    type Value = OptionValueTree<T::Value>;

    fn new_value(&self, runner: &mut TestRunner)
        -> Result<Self::Value, String>
    {
        Ok(OptionValueTree {
            prev: None,
            pick:
                if weighted(self.prob).new_value(runner)?.current() {
                    Some(self.strat.new_value(runner)?)
                } else {
                    None
                }
        })
    }
}

impl<T: ValueTree> ValueTree for OptionValueTree<T> {
    type Value = Option<T::Value>;

    fn current(&self) -> Self::Value {
        self.pick.as_ref().map(ValueTree::current)
    }

    fn simplify(&mut self) -> bool {
        self.pick.take().map_or(false, |mut inner| {
            if inner.simplify() {
                self.pick = Some(inner);
                self.prev = None;
            } else {
                self.pick = None;
                self.prev = Some(inner);
            };
            true
        })
    }

    fn complicate(&mut self) -> bool {
        if let Some(pick) = self.prev.take() {
            self.pick = Some(pick);
            true
        } else {
            self.pick.as_mut().unwrap().complicate()
        }
    }
}

//============================================================================//
// CharRanges:
//============================================================================//

type CharRanges<'a> = &'a [(char, char)];

pub fn from_char_ranges<'a>(preferred: CharRanges<'a>, ranges: CharRanges<'a>
) -> CharStrategy<'a> {
    CharStrategy::new(
        Cow::Borrowed(&[]),
        Cow::Borrowed(preferred),
        Cow::Borrowed(ranges),
    )
}

//============================================================================//
// Macros:
//============================================================================//

macro_rules! prop_compose_enum {
    ($gen: ident -> $rtype: ty [$($item:expr),+ $(,)*]) => {
        pub fn $gen() -> Union<Just<$rtype>> {
            Union::new(vec![$(Just($item)),*])
        }
    }
}

//============================================================================//
// Tokens:
//============================================================================//

pub fn gen_token() -> BoxedStrategy<Token<Box<str>>> {
    prop_oneof![
      gen_ctoken().prop_map(Const)
    , gen_axis().prop_map(Axis)
    , gen_name_test().prop_map(NTest)
    , gen_node_type().prop_map(NType)
    , gen_qname().prop_map(FnName)
    , gen_str_lit().prop_map(Literal)
    , gen_number().prop_map(Number)
    , gen_qname().prop_map(VarRef)
    ].boxed()
}

prop_compose_enum!(gen_axis -> AxisName [
    Child,
    Parent,
    SelfAxis,
    Namespace,
    Attribute,
    AncestorOrSelf,
    Ancestor,
    DescendantOrSelf,
    Descendant,
    FollowingSibling,
    Following,
    PrecedingSibling,
    Preceding,
]);

prop_compose_enum!(gen_node_type -> NodeType [
    Text, Node, Comment, ProcIns
]);

prop_compose_enum!(gen_ctoken -> CToken [
    And,
    AtSign,
    Comma,
    CurrentNode,
    Divide,
    DoubleSlash,
    Equal,
    GreaterThan,
    GreaterThanOrEqual,
    LeftBracket,
    LeftParen,
    LessThan,
    LessThanOrEqual,
    MinusSign,
    Multiply,
    NotEqual,
    Or,
    ParentNode,
    Pipe,
    PlusSign,
    Remainder,
    RightBracket,
    RightParen,
    Slash,
]);

pub fn gen_name_start_char<'a>() -> CharStrategy<'a> {
    const RANGES: [(char, char); 15] = [
          ('a', 'z')
        , ('A', 'Z')
        , ('_', '_')
        , ('\u{C0}', '\u{D6}')
        , ('\u{D8}', '\u{F6}')
        , ('\u{F8}', '\u{2FF}')
        , ('\u{370}', '\u{37D}')
        , ('\u{37F}', '\u{1FFF}')
        , ('\u{200C}', '\u{200D}')
        , ('\u{2070}', '\u{218F}')
        , ('\u{2C00}', '\u{2FEF}')
        , ('\u{3001}', '\u{D7FF}')
        , ('\u{F900}', '\u{FDCF}')
        , ('\u{FDF0}', '\u{FFFD}')
        , ('\u{10000}', '\u{EFFFF}')
    ];
    from_char_ranges(&RANGES[3..], &RANGES)
}

pub fn gen_name_mid_char<'a>() -> CharStrategy<'a> {
    const RANGES: [(char, char); 6] = [
            ('0', '9')
        , ('-', '-')
        , ('.', '.')
        , ('\u{B7}', '\u{B7}')
        , ('\u{300}', '\u{36F}')
        , ('\u{203F}', '\u{2040}')
    ];
    from_char_ranges(&RANGES[1..], &RANGES)
}

pub fn gen_name_char<'a>() -> Union<CharStrategy<'a>> {
    gen_name_start_char().prop_union(gen_name_mid_char())
}

pub fn gen_nc_name() -> BoxedStrategy<Box<str>> {
    gen_name_start_char().prop_flat_map(move |start|
        prop::collection::vec(gen_name_char(), 0..100).prop_map(
            move |rest| {
                let mut s = String::with_capacity(rest.len() + 1);
                s.push(start);
                s.extend(rest);
                s.into_boxed_str()
            }
        )
    ).boxed()
}

prop_compose! {
    [pub] fn gen_qname()(prefix in optional_weighted(gen_nc_name(), 1.0 / 3.0),
                        local in gen_nc_name()) -> QName<Box<str>> {
        QName::new(prefix, local)
    }
}

prop_compose! {
    [pub] fn gen_name_test()(prefix in optional(gen_nc_name()),
                            local in optional_weighted(gen_nc_name(), 1.0 / 4.0))
                    -> NameTest<Box<str>> {
        NameTest::new(prefix, local)
    }
}

prop_compose! {
    [pub] fn gen_number()(num in 0.0..) -> f64 { num }
}

prop_compose! {
    [pub] fn gen_str_lit()(lit in "[^\"]*") -> Box<str> {
        lit.into()
    }
}
