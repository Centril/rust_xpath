//============================================================================//
// Imports:
//============================================================================//

use super::util::to_boxed_str;
use self::Token::*;
use self::CToken::*;

//============================================================================//
// Token types:
//============================================================================//

/// Models `[6] AxisName`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AxisName {
    Ancestor,         // ancestor::
    AncestorOrSelf,   // ancestor-or-self::
    Attribute,        // attribute::
    Child,            // child::
    Descendant,       // descendant::
    DescendantOrSelf, // descendant-or-self::
    Following,        // following-sibling::
    FollowingSibling, // following::
    Namespace,        // namespace::
    Parent,           // parent::
    Preceding,        // preceding::
    PrecedingSibling, // preceding-sibling::
    SelfAxis,         // self::
}

/// Models `[38] NodeType`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NodeType {
    Comment,
    Node,
    Text,
    ProcIns,
}

/// Models a [`QName`].
///
/// [`QName`]: https://www.w3.org/TR/REC-xml-names/#ns-qualnames
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct QName<S: AsRef<str>> {
    pub prefix: Option<S>,
    pub local: S,
}

/// Models `[37] NameTest`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NameTest<S: AsRef<str>> {
    pub prefix: Option<S>,
    pub local: Option<S>,
}

/// Models: Operator + ( + ) + | + [ + ] + . + .. + @ + ,
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

/// Models the lexical structure of xpath, `[28] ExprToken`.
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub enum Token<S: AsRef<str>> {
    // All constants: Operators + what's left.
    Const(CToken),

    /// An AxisName token.
    Axis(AxisName),

    // A NameTest token.
    NTest(NameTest<S>),

    // A NodeType token.
    NType(NodeType),

    /// A function name token.
    FnName(QName<S>),

    /// A quoted literal token.
    Literal(S),

    /// A number literal token.
    Number(f64),

    /// A variable reference token.
    VarRef(QName<S>),
}

//============================================================================//
// Implementations
//============================================================================//

impl<S: AsRef<str>> NameTest<S> {
    pub fn new(prefix: Option<S>, local: Option<S>) -> Self {
        Self { prefix, local }
    }
}

impl<S: AsRef<str>> QName<S> {
    pub fn new(prefix: Option<S>, local: S) -> Self {
        Self { prefix, local }
    }
}

impl<S: AsRef<str>> From<S> for NameTest<S> {
    fn from(local_part: S) -> Self {
        Self::new(None, Some(local_part))
    }
}

impl<S: AsRef<str>> From<S> for QName<S> {
    fn from(local_part: S) -> Self {
        Self::new(None, local_part)
    }
}

impl<S: AsRef<str>> Token<S> {
    /// Yields true if token precedes a node test.
    pub fn precedes_node_test(&self) -> bool {
        match *self {
            Const(AtSign) | Axis(..) => true,
            _ => false,
        }
    }

    /// Yields true if this token precedes an expression, i.e: an expression
    /// must come after this.
    pub fn precedes_expression(&self) -> bool {
        match *self {
            Const(LeftParen) | Const(LeftBracket) => true,
            _ => false,
        }
    }

    /// Yields true if the token is an operator token.
    pub fn is_operator(&self) -> bool {
        match *self {
            Const(ref c) => match *c {
                Slash |
                DoubleSlash |
                PlusSign |
                MinusSign |
                Pipe |
                Equal |
                NotEqual |
                LessThan |
                LessThanOrEqual |
                GreaterThan |
                GreaterThanOrEqual |
                And |
                Or |
                Remainder |
                Divide |
                Multiply => true,
                _ => false,
            },
            _ => false,
        }
    }
}

//============================================================================//
// Functor API
//============================================================================//

impl<S: AsRef<str>> NameTest<S> {
    /// Applies a pure function mapping the string type of the NameTest.
    pub fn map<F, T>(self, f: F) -> NameTest<T>
    where
        T: AsRef<str>,
        F: Fn(S) -> T,
    {
        NameTest::new(self.prefix.map(&f), self.local.map(&f))
    }
}

impl<S: AsRef<str>> QName<S> {
    /// Applies a pure function mapping the string type of the QName.
    pub fn map<F, T>(self, f: F) -> QName<T>
    where
        T: AsRef<str>,
        F: Fn(S) -> T,
    {
        QName::new(self.prefix.map(&f), f(self.local))
    }
}

impl<S: AsRef<str>> Token<S> {
    /// Applies a pure function mapping the string type of the Token.
    /// This is a covariant endofunctor in the sense that the category mapped
    /// over is one with objects : AsRef<str>.
    pub fn map<F, T>(self, f: F) -> Token<T>
    where
        T: AsRef<str>,
        F: Fn(S) -> T,
    {
        match self {
            Const(c) => Const(c),
            Axis(a) => Axis(a),
            NType(nt) => NType(nt),
            Number(n) => Number(n),
            NTest(nt) => NTest(nt.map(f)),
            FnName(qn) => FnName(qn.map(f)),
            Literal(l) => Literal(f(l)),
            VarRef(qn) => VarRef(qn.map(f)),
        }
    }
}

//============================================================================//
// Boxing Strings API
//============================================================================//

impl<S: AsRef<str>> NameTest<S> {
    /// Produces a semantically equivalent NameTest using boxed strings instead
    /// wherever applicable.
    pub fn boxed_str(self) -> NameTest<Box<str>> {
        self.map(to_boxed_str)
    }
}

impl<S: AsRef<str>> QName<S> {
    /// Produces a semantically equivalent QName using boxed strings instead
    /// wherever applicable.
    pub fn boxed_str(self) -> QName<Box<str>> {
        self.map(to_boxed_str)
    }
}

impl<S: AsRef<str>> Token<S> {
    /// Produces a semantically equivalent token using boxed strings instead
    /// wherever applicable.
    pub fn boxed_str(self) -> Token<Box<str>> {
        self.map(to_boxed_str)
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
    println!("size_of QName:    \t {:?}", size_of::<QName<&str>>());
    println!("size_of NameTest: \t {:?}", size_of::<NameTest<&str>>());
    println!("size_of Token:    \t {:?}", size_of::<Token<&str>>());
}
*/
