//============================================================================//
// Imports:
//============================================================================//

use std::fmt::{Display, Formatter, Result};

use super::tokens::*;
use super::tokens::Token::*;
use super::tokens::CToken::*;
use super::tokens::AxisName::*;
use super::tokens::NodeType::*;

//============================================================================//
// Public API:
//============================================================================//

pub trait ShowAsStr {
    fn show(&self) -> &str;
}

impl<S: AsRef<str>> Display for Token<S> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match *self {
            Const(tok) => write!(f, "{}", tok),
            Axis(axis) => write!(f, "{}", axis),
            NTest(ref nt) => write!(f, "{}", nt),
            NType(nt) => write!(f, "{}", nt),
            FnName(ref fun) => write!(f, "{}", fun),
            Literal(ref lit) => write!(f, "\"{}\"", lit.as_ref()),
            Number(num) => write!(f, "{}", num), // TODO: Handle negative.
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
            Equal => "==",
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
// Internal
//============================================================================//

fn display_prefix<S: AsRef<str>>(op: &Option<S>, f: &mut Formatter) -> Result {
    op.as_ref()
        .map_or_else(|| Ok(()), |prefix| write!(f, "{}:", prefix.as_ref()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck::{Arbitrary, Gen};

    impl Arbitrary for AxisName {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            *g.choose(&[
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
            ]).unwrap()
        }
    }

    impl Arbitrary for NodeType {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            *g.choose(&[Text, Node, Comment, ProcIns]).unwrap()
        }
    }

    impl Arbitrary for CToken {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            *g.choose(&[
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
            ]).unwrap()
        }
    }

    use lexer::{Error, Lexer, StrToken};
    use std::fmt::Debug;
    use std::result::Result;

    type VTok<'a> = Vec<StrToken<'a>>;

    fn no_complete<T: Debug>(x: T) -> ! {
        panic!("parser did not complete, because:\n{:?}\n", x);
    }

    /// Lexes the input completely into a vector.
    fn all_tokens_raw(i: &str) -> Result<VTok, Error> {
        Lexer::new(i).collect()
    }

    /// Lexes the input completely and ensures the lexer did not error.
    fn all_tokens(i: &str) -> VTok {
        all_tokens_raw(i).unwrap_or_else(|e| no_complete(e))
    }

    #[quickcheck]
    fn axis_show_lex_is_identity(orig: AxisName) -> bool {
        if let Axis(lex) = all_tokens(orig.show())[0] {
            orig == lex
        } else {
            false
        }
    }

    #[quickcheck]
    fn ntype_show_lex_is_identity(orig: NodeType) -> bool {
        if let NType(lex) = all_tokens(orig.show())[0] {
            orig == lex
        } else {
            false
        }
    }

    #[quickcheck]
    fn ctoken_show_lex_is_identity(orig: CToken) -> bool {
        if let Const(lex) = all_tokens(orig.show())[0] {
            orig == lex
        } else {
            false
        }
    }


    /*
*/
}
