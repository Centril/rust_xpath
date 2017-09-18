//! Provides utlities and generators for property based testing with proptest.

//============================================================================//
// Imports:
//============================================================================//

use std::borrow::Cow;

use proptest::prelude::*;
use proptest::char::CharStrategy;
use proptest::option;
use proptest::strategy::Union as UnionStrategy;

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
        pub fn $gen() -> UnionStrategy<Just<$rtype>> {
            UnionStrategy::new(vec![$(Just($item)),*])
        }
    }
}

//============================================================================//
// General strategies:
//============================================================================//

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

//============================================================================//
// NCName:
//============================================================================//

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
pub fn gen_name_char<'a>() -> UnionStrategy<CharStrategy<'a>> {
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

//============================================================================//
// Tokens:
//============================================================================//

pub mod tokens {
    use super::*;
    use tokens::*;          
    use tokens::Token::*;   
    use tokens::CToken::*;  
    use tokens::AxisName::*;
    use tokens::NodeType::*;

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
            gen_axisname().prop_map(Axis),
            gen_name_test().prop_map(NTest),
            gen_node_type().prop_map(NType),
            gen_qname().prop_map(FnName),
            gen_str_lit().prop_map(Literal),
            gen_number().prop_map(Number),
            gen_qname().prop_map(VarRef)
        ].boxed()
    }

    // Strategy for `AxisName`:
    prop_compose_enum!(gen_axisname -> AxisName [
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

    prop_compose! {
        /// Strategy for `QName`s:
        [pub] fn gen_qname()
                (prefix in option::weighted(1.0 / 3.0, gen_nc_name()),
                 local in gen_nc_name())
                -> QName<Box<str>>
        {
            QName::new(prefix, local)
        }
    }

    prop_compose! {
        /// Stategy for `NameTest`s:
        [pub] fn gen_name_test()
                (prefix in option::of(gen_nc_name()),
                 local in option::weighted(1.0 / 4.0, gen_nc_name()))
                -> NameTest<Box<str>>
        {
            NameTest::new(prefix, local)
        }
    }
}

//============================================================================//
// Expr:
//============================================================================//

pub mod expr {
    use super::*;

    use expr::*;
    use expr::Axis::*;
    use expr::BinaryOp::*;
    use expr::CoreFunction::*;

    // Strategy for `Axis`:
    prop_compose_enum!(gen_axis -> Axis [
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

    // Strategy for `PrincipalNodeType`:
    prop_compose_enum!(gen_principal_node_type -> PrincipalNodeType [
        PrincipalNodeType::Attribute,
        PrincipalNodeType::Element,
        PrincipalNodeType::Namespace,
    ]);

    // Strategy for `BinaryOp`:
    prop_compose_enum!(gen_binary_op -> BinaryOp [
        Or,    
        And,   
        Eq,    
        NEq,   
        Lt,    
        Gt,    
        LEq,   
        GEq,   
        Add,   
        Sub,   
        Mul,   
        Div,   
        Rem,   
        Union, 
        Filter,
    ]);

    // Strategy for `CoreFunction`:
    prop_compose_enum!(gen_core_function -> CoreFunction [
        Last,
        Position,
        Count,
        Id,
        LocalName,
        NamespaceUri,
        Name,
        String,
        Concat,
        StartsWith,
        Contains,
        SubstringBefore,
        SubstringAfter,
        Substring,
        StringLength,
        NormalizeSpace,
        Translate,
        Boolean,
        Not,
        True,
        False,
        Lang,
        Number,
        Sum,
        Floor,
        Ceiling,
        Round,
    ]);

    /// Strategy for a `LiteralValue`:
    pub fn gen_literal_value() -> BoxedStrategy<LiteralValue> {
        prop_oneof![
            gen_number().prop_map(LiteralValue::Number),
            gen_str_lit().prop_map(LiteralValue::String),
        ].boxed()
    }

    prop_compose! {
        /// Strategy for `QName`s:
        [pub] fn gen_qname()
                (prefix in option::weighted(1.0 / 3.0, gen_nc_name()),
                 local in gen_nc_name())
                -> QName
        {
            QName::new(prefix, local)
        }
    }

    prop_compose! {
        /// Stategy for `NameTest`s:
        [pub] fn gen_name_test()
                (prefix in option::of(gen_nc_name()),
                 local in option::weighted(1.0 / 4.0, gen_nc_name()))
                -> NameTest
        {
            NameTest::new(prefix, local)
        }
    }

    pub fn gen_node_test() -> BoxedStrategy<NodeTest> {
        use expr::NodeTest::*;
        prop_oneof![
            Just(Node),
            Just(Text),
            Just(Comment),
            option::of(gen_str_lit()).prop_map(ProcIns),
            gen_name_test().prop_map(Attribute),
            gen_name_test().prop_map(Namespace),
            gen_name_test().prop_map(Element),
        ].boxed()
    }

    prop_compose!{
        [pub] fn gen_steps()
                (axis in gen_axis(),
                 node_test in gen_node_test(),
                 )//predicates in panic!())
                -> StepsB
        {
            StepsB::new_steps(axis, node_test, panic!()) // TODO!
        }
    }

    /*
    #[derive(PartialEq, Clone, Debug)]
pub struct StepsB<P = B, S = B, L = B>
where
    P: AsRef<str>,
    S: AsRef<str>,
    L: AsRef<str>,
{
    pub axis:       Axis,
    pub node_test:  NodeTest<P, S>,
    pub predicates: Box<[ExprB<P, S, L>]>,
}
*/

    fn gen_expr() -> BoxedStrategy<ExprB> {
        use expr::ExprB::*;

        let leaf = prop_oneof![
            Just(RootNode),
            Just(ContextNode),
            gen_literal_value().prop_map(Literal),
            gen_qname().prop_map(Var),
        ];

/*
pub enum ExprB {
    Apply(QName<P, S>, Box<[ExprB<P, S, L>]>),
    Path(Box<ExprB<P, S, L>>, Box<[StepsB<P, S, L>]>),
}
*/

        leaf.prop_recursive(
            8,   // 8 levels deep
            256, // Shoot for maximum size of 256 nodes
            10,  // We put up to 10 items per collection
            |inner| {
                prop_oneof![
                    (gen_binary_op(), inner.clone(), inner.clone())
                        .prop_map(|(op, lhs, rhs)|
                            ExprB::new_bin(op, Box::new(lhs), Box::new(rhs))),
                    inner.clone()
                         .prop_map(|expr| ExprB::new_neg(Box::new(expr))),
                ].boxed()
            }
        ).boxed()

        /*
        leaf.prop_recursive(
            
            
            
            |inner| {
                prop_oneof![
          // Take the inner strategy and make the two recursive cases.
          prop::collection::vec(inner.clone(), 0..10)
              .prop_map(Json::Array),
          prop::collection::hash_map(".*", inner, 0..10)
              .prop_map(Json::Map),
      ].boxed()
            },
        )
            .boxed()
*/    }



}
