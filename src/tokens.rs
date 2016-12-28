//============================================================================//
// Token types:
//============================================================================//

#[derive(PartialEq, Clone, Debug)]
pub enum AxisName {
    Ancestor,           // ancestor::
    AncestorOrSelf,     // ancestor-or-self::
    Attribute,          // attribute::
    Child,              // child::
    Descendant,         // descendant::
    DescendantOrSelf,   // descendant-or-self::
    Following,          // following-sibling::
    FollowingSibling,   // following::
    Namespace,          // namespace::
    Parent,             // parent::
    Preceding,          // preceding::
    PrecedingSibling,   // preceding-sibling::
    SelfAxis,           // self::
}

#[derive(PartialEq, Clone, Debug)]
pub enum NodeType {
    Comment,
    Node,
    Text,
    ProcIns
}

//#[derive(PartialEq, Clone, Debug)]
//pub struct NameTest<S: AsRef<str>>(pub Option<S>, pub Option<S>);

#[derive(PartialEq, Clone, Debug)]
pub struct QName<S: AsRef<str>>(pub Option<S>, pub S);

#[derive(PartialEq, Clone, Debug)]
pub enum CToken {
    And,                // and
    AtSign,             // @
    Comma,              // ,
    CurrentNode,        // .
    Divide,             // div
    DoubleSlash,        // //
    Equal,              // =
    GreaterThan,        // >
    GreaterThanOrEqual, // >=
    LeftBracket,        // [
    LeftParen,          // (
    LessThan,           // <
    LessThanOrEqual,    // <=
    MinusSign,          // -
    Multiply,           // *
    NotEqual,           // !=
    Or,                 // or
    ParentNode,         // ..
    Pipe,               // |
    PlusSign,           // +
    Remainder,          // mod
    RightBracket,       // ]
    RightParen,         // )
    Slash,              // /
}

#[derive(PartialEq, Clone, Debug)]
pub enum Token<S: AsRef<str>> {
    // Constants:
    Const(CToken),
    Axis(AxisName),

    // NameTest:
    Wildcard,
    NSWildcard(S),
    LocalPart(S),
    NSLocalPart(S, S),
    //NTest(NameTest<S>),

    // Compound:
    NType(NodeType),
    FnName(QName<S>),
    Literal(S),
    Number(f64),
    VarRef(QName<S>),
}

use self::Token::*;

impl<S: AsRef<str>> Token<S> {
    pub fn precedes_node_test(&self) -> bool {
        match *self {
              Const(CToken::AtSign)
            | Axis(..)
              => true,
            _ => false,
        }
    }

    pub fn precedes_expression(&self) -> bool {
        match *self {
              Const(CToken::LeftParen)
            | Const(CToken::LeftBracket)
              => true,
            _ => false,
        }
    }

    pub fn is_operator(& self) -> bool {
        match *self {
              Const(CToken::Slash)
            | Const(CToken::DoubleSlash)
            | Const(CToken::PlusSign)
            | Const(CToken::MinusSign)
            | Const(CToken::Pipe)
            | Const(CToken::Equal)
            | Const(CToken::NotEqual)
            | Const(CToken::LessThan)
            | Const(CToken::LessThanOrEqual)
            | Const(CToken::GreaterThan)
            | Const(CToken::GreaterThanOrEqual)
            | Const(CToken::And)
            | Const(CToken::Or)
            | Const(CToken::Remainder)
            | Const(CToken::Divide)
            | Const(CToken::Multiply)
              => true,
            _ => false,
        }
    }
}

/*
#[test]
fn size_of() {
    use std::mem::size_of;
    println!("tokens.rs!");
    println!("size_of CToken:   \t {:?}", size_of::<CToken>());
    println!("size_of AxisName: \t {:?}", size_of::<AxisName>());
    println!("size_of NodeType: \t {:?}", size_of::<NodeType>());
    //println!("size_of NameTest: \t {:?}", size_of::<NameTest<&str>>());
    println!("size_of Token:    \t {:?}", size_of::<Token<&str>>());
}
*/