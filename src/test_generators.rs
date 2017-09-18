//! Provides utlities and generators for property based testing with proptest.

//============================================================================//
// Imports:
//============================================================================//

use std::borrow::Cow;

use proptest::prelude::*;
use proptest::char::CharStrategy;
use proptest::option;
use proptest::strategy::Union;

use super::tokens::*;
use super::tokens::Token::*;
use super::tokens::CToken::*;
use super::tokens::AxisName::*;
use super::tokens::NodeType::*;

//============================================================================//
// CharRanges:
//============================================================================//

/// A list of ranges of `char`s where both end points are inclusive.
type CharRanges<'a> = &'a [(char, char)];

/// Constructs a `CharStrategy` from a list of preferred `CharRanges` and
/// the total set of allowed `CharRanges`. `preferred` should be a sublist of
/// `ranges` for it to have any effect.
pub fn from_char_ranges<'a>(
    preferred: CharRanges<'a>,
    ranges: CharRanges<'a>,
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

/// Creates a strategy for a simple flat sum type.
macro_rules! prop_compose_enum {
    ($gen: ident -> $rtype: ty [$($item:expr),+ $(,)*]) => {
        /// Yields a strategy for the type.
        pub fn $gen() -> Union<Just<$rtype>> {
            Union::new(vec![$(Just($item)),*])
        }
    }
}

//============================================================================//
// Tokens:
//============================================================================//

prop_compose! {
    /// Strategy for `Token`s:
    [pub] fn gen_tokens()(vec in prop::collection::vec(gen_token(), 0..100))
                       -> Vec<Token<Box<str>>> {
        vec
    }
}

/// Strategy for a `Token`.
pub fn gen_token() -> BoxedStrategy<Token<Box<str>>> {
    prop_oneof![
        gen_ctoken().prop_map(Const),
        gen_axis().prop_map(Axis),
        gen_name_test().prop_map(NTest),
        gen_node_type().prop_map(NType),
        gen_qname().prop_map(FnName),
        gen_str_lit().prop_map(Literal),
        gen_number().prop_map(Number),
        gen_qname().prop_map(VarRef)
    ].boxed()
}

// Strategy for `AxisName`:
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

// Strategy for `NodeType`:
prop_compose_enum!(gen_node_type -> NodeType [
    Text, Node, Comment, ProcIns
]);

// Strategy for `CToken`:
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

/// Strategy for a `NameStartChar`:
pub fn gen_name_start_char<'a>() -> CharStrategy<'a> {
    const RANGES: [(char, char); 15] = [
        ('a', 'z'),
        ('A', 'Z'),
        ('_', '_'),
        ('\u{C0}', '\u{D6}'),
        ('\u{D8}', '\u{F6}'),
        ('\u{F8}', '\u{2FF}'),
        ('\u{370}', '\u{37D}'),
        ('\u{37F}', '\u{1FFF}'),
        ('\u{200C}', '\u{200D}'),
        ('\u{2070}', '\u{218F}'),
        ('\u{2C00}', '\u{2FEF}'),
        ('\u{3001}', '\u{D7FF}'),
        ('\u{F900}', '\u{FDCF}'),
        ('\u{FDF0}', '\u{FFFD}'),
        ('\u{10000}', '\u{EFFFF}'),
    ];
    from_char_ranges(&RANGES[3..], &RANGES)
}

/// Strategy for a `NameChar` which is not also a `NameStartChar`.
pub fn gen_name_mid_char<'a>() -> CharStrategy<'a> {
    const RANGES: [(char, char); 6] = [
        ('0', '9'),
        ('-', '-'),
        ('.', '.'),
        ('\u{B7}', '\u{B7}'),
        ('\u{300}', '\u{36F}'),
        ('\u{203F}', '\u{2040}'),
    ];
    from_char_ranges(&RANGES[1..], &RANGES)
}

/// Strategy for a `NameChar` ::= `NameStartChar` | `NameMidChar`.
pub fn gen_name_char<'a>() -> Union<CharStrategy<'a>> {
    gen_name_start_char().prop_union(gen_name_mid_char())
}

/// Strategy for a `NCName` ::= `NameStartChar` `NameChar`*
pub fn gen_nc_name() -> BoxedStrategy<Box<str>> {
    gen_name_start_char().prop_flat_map(move |start| {
        prop::collection::vec(gen_name_char(), 0..100).prop_map(move |rest| {
            let mut s = String::with_capacity(rest.len() + 1);
            s.push(start);
            s.extend(rest);
            s.into_boxed_str()
        })
    })
                         .boxed()
}

prop_compose! {
    /// Strategy for `QName`s:
    [pub] fn gen_qname()(prefix in option::weighted(1.0 / 3.0, gen_nc_name()),
                        local in gen_nc_name()) -> QName<Box<str>> {
        QName::new(prefix, local)
    }
}

prop_compose! {
    /// Stategy for `NameTest`s:
    [pub] fn gen_name_test()(prefix in option::of(gen_nc_name()),
                            local in option::weighted(1.0 / 4.0, gen_nc_name()))
                    -> NameTest<Box<str>> {
        NameTest::new(prefix, local)
    }
}

prop_compose! {
    /// Strategy for a positive number:
    [pub] fn gen_number()(num in 0.0..) -> f64 { num }
}

prop_compose! {
    /// Strategy for a string literal:
    [pub] fn gen_str_lit()(lit in "[^\"]*") -> Box<str> {
        lit.into()
    }
}
