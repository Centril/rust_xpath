//============================================================================//
// Imports:
//============================================================================//

use std::fmt::{Display, Formatter, Result};

use super::util::to_boxed_str;
use self::Token::*;
use self::CToken::*;
use self::AxisName::*;
use self::NodeType::*;

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
    pub local:  S,
}

/// Models `[37] NameTest`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NameTest<S: AsRef<str>> {
    pub prefix: Option<S>,
    pub local:  Option<S>,
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

/// A [`Token`], with `&'a str` as the backing type for strings.
///
/// [`Token`]: struct.Token.html
pub(crate) type StrToken<'a> = Token<&'a str>;

//============================================================================//
// Display implementations:
//============================================================================//

/// A type that can describe itself immediately as a string slice.
pub trait ShowAsStr {
    /// Describe/show the object as a string slice without allocation.
    fn show(&self) -> &str;
}

impl<S: AsRef<str>> Display for Token<S> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match *self {
            Const(tok) => write!(f, "{}", tok),
            Axis(axis) => write!(f, "{}", axis),
            NTest(ref nt) => write!(f, "{}", nt),
            NType(nt) => write!(f, "{}", nt),
            FnName(ref fun) => write!(f, "{}(", fun),
            Literal(ref lit) => write!(f, "\"{}\"", lit.as_ref()),
            Number(num) => write!(f, "{}", num),
            VarRef(ref var) => write!(f, "${}", var),
        }
    }
}

impl<S: AsRef<str>> Display for QName<S> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        display_prefix(&self.prefix, f)?;
        write!(f, "{}", self.local.as_ref())
    }
}

impl<S: AsRef<str>> Display for NameTest<S> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        display_prefix(&self.prefix, f)?;
        write!(f, "{}", self.local.as_ref().map_or("*", |lp| lp.as_ref()))
    }
}

impl ShowAsStr for AxisName {
    fn show(&self) -> &str {
        match *self {
            Child => "child::",
            Parent => "parent::",
            SelfAxis => "self::",
            Namespace => "namespace::",
            Attribute => "attribute::",
            AncestorOrSelf => "ancestor-or-self::",
            Ancestor => "ancestor::",
            DescendantOrSelf => "descendant-or-self::",
            Descendant => "descendant::",
            FollowingSibling => "following-sibling::",
            Following => "following::",
            PrecedingSibling => "preceding-sibling::",
            Preceding => "preceding::",
        }
    }
}

impl ShowAsStr for NodeType {
    fn show(&self) -> &str {
        match *self {
            Text => "text",
            Node => "node",
            Comment => "comment",
            ProcIns => "processing-instruction",
        }
    }
}

impl ShowAsStr for CToken {
    fn show(&self) -> &str {
        match *self {
            And => "and",
            AtSign => "@",
            Comma => ",",
            CurrentNode => ".",
            Divide => "div",
            DoubleSlash => "//",
            Equal => "=",
            GreaterThan => ">",
            GreaterThanOrEqual => ">=",
            LeftBracket => "[",
            LeftParen => "(",
            LessThan => "<",
            LessThanOrEqual => "<=",
            MinusSign => "-",
            Multiply => "*",
            NotEqual => "!=",
            Or => "or",
            ParentNode => "..",
            Pipe => "|",
            PlusSign => "+",
            Remainder => "mod",
            RightBracket => "]",
            RightParen => ")",
            Slash => "/",
        }
    }
}

macro_rules! display_show {
    ($type: ident) => {
        impl Display for $type {
            fn fmt(&self, f: &mut Formatter) -> Result {
                write!(f, "{}", self.show())
            }
        }
    };
}

display_show!(AxisName);
display_show!(CToken);
display_show!(NodeType);

//============================================================================//
// Display implementations, Internal
//============================================================================//

fn display_prefix<S: AsRef<str>>(op: &Option<S>, f: &mut Formatter) -> Result {
    op.as_ref()
      .map_or_else(|| Ok(()), |prefix| write!(f, "{}:", prefix.as_ref()))
}

//============================================================================//
// Implementations
//============================================================================//

impl<S: AsRef<str>> NameTest<S> {
    /// Constructs a new NameTest.
    pub fn new(prefix: Option<S>, local: Option<S>) -> Self {
        Self { prefix, local }
    }
}

impl<S: AsRef<str>> QName<S> {
    /// Constructs a new QName.
    pub fn new(prefix: Option<S>, local: S) -> Self { Self { prefix, local } }
}

impl<S: AsRef<str>> From<S> for NameTest<S> {
    fn from(local_part: S) -> Self { Self::new(None, Some(local_part)) }
}

impl<S: AsRef<str>> From<S> for QName<S> {
    fn from(local_part: S) -> Self { Self::new(None, local_part) }
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

    /// If following the lexing of this token a lexer should bias in favour
    /// of named operators (*, or, and, mod, div) instead of NameTest.
    ///
    /// This occurs when this token is not an operator, and not followed by
    /// a
    /// node test and does not precede an expression.
    ///
    /// See http://www.w3.org/TR/xpath/#exprlex for more details.
    pub fn prefer_op_names(&self) -> bool {
        !(self.precedes_node_test() || self.precedes_expression() ||
            self.is_operator())
    }
}

//============================================================================//
// Functor API
//============================================================================//

impl<S: AsRef<str>> NameTest<S> {
    /// Applies a pure function mapping the string type of the NameTest.
    pub fn map<'a, F, T>(&'a self, f: F) -> NameTest<T>
    where
        T: AsRef<str>,
        F: Fn(&'a S) -> T,
    {
        NameTest::new(self.prefix.as_ref().map(&f), self.local.as_ref().map(&f))
    }
}

impl<S: AsRef<str>> QName<S> {
    /// Applies a pure function mapping the string type of the QName.
    pub fn map<'a, F, T>(&'a self, f: F) -> QName<T>
    where
        T: AsRef<str>,
        F: Fn(&'a S) -> T,
    {
        QName::new(self.prefix.as_ref().map(&f), f(&self.local))
    }
}

impl<S: AsRef<str>> Token<S> {
    /// Applies a pure function mapping the string type of the Token.
    /// This is a covariant endofunctor in the sense that the category
    /// mapped
    /// over is one with objects : AsRef<str>.
    pub fn map<'a, F, T>(&'a self, f: F) -> Token<T>
    where
        T: AsRef<str>,
        F: Fn(&'a S) -> T,
    {
        match *self {
            Const(c) => Const(c),
            Axis(a) => Axis(a),
            NType(nt) => NType(nt),
            Number(n) => Number(n),
            NTest(ref nt) => NTest(nt.map(f)),
            FnName(ref qn) => FnName(qn.map(f)),
            Literal(ref l) => Literal(f(l)),
            VarRef(ref qn) => VarRef(qn.map(f)),
        }
    }
}

//============================================================================//
// Functor API, AsRef<str> -> &str :
//============================================================================//

impl<S: AsRef<str>> NameTest<S> {
    /// Produces a semantically equivalent NameTest using borrowed strings
    /// instead wherever applicable.
    pub fn borrowed(&self) -> NameTest<&str> { self.map(|s| s.as_ref()) }
}

impl<S: AsRef<str>> QName<S> {
    /// Produces a semantically equivalent QName using borrowed strings
    /// instead wherever applicable.
    pub fn borrowed(&self) -> QName<&str> { self.map(|s| s.as_ref()) }
}

impl<S: AsRef<str>> Token<S> {
    /// Produces a semantically equivalent Token using borrowed strings
    /// instead wherever applicable.
    pub fn borrowed(&self) -> Token<&str> { self.map(|s| s.as_ref()) }
}

//============================================================================//
// Boxing Strings API
//============================================================================//

impl<S: AsRef<str>> NameTest<S> {
    /// Produces a semantically equivalent NameTest using boxed strings
    /// instead
    /// wherever applicable.
    pub fn boxed_str(self) -> NameTest<Box<str>> { self.map(to_boxed_str) }
}

impl<S: AsRef<str>> QName<S> {
    /// Produces a semantically equivalent QName using boxed strings instead
    /// wherever applicable.
    pub fn boxed_str(self) -> QName<Box<str>> { self.map(to_boxed_str) }
}

impl<S: AsRef<str>> Token<S> {
    /// Produces a semantically equivalent token using boxed strings instead
    /// wherever applicable.
    pub fn boxed_str(self) -> Token<Box<str>> { self.map(to_boxed_str) }
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
