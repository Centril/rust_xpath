//============================================================================//
// Imports:
//============================================================================//

// std:
use std::{error, fmt};

use phf;

use nom::*;
use nom::IResult::*;

// tokens:
use super::tokens::*;
use super::tokens::CToken::*;
use super::tokens::AxisName::*;
use super::tokens::NodeType::*;
use super::tokens::Token::*;

//============================================================================//
// Errors
//============================================================================//

#[derive(PartialEq, Debug, Clone)]
pub enum LexerError {
    ExpectedQuote,
    MismatchedQuoteCharacters,
    ExpectedNumber,
    ExpectedCurrentNode,
    ExpectedNamedOperator,
    ExpectedAxis,
    ExpectedAxisSeparator,
    ExpectedNodeTest,
    ExpectedQName,
    ExpectedNameTest,
    ExpectedVariableReference,
    ExpectedToken,
    ExpectedLeftParenthesis,
    UnableToCreateToken,
}

impl error::Error for LexerError {
    fn description(&self) -> &str {
        use self::LexerError::*;
        match *self {
            ExpectedQuote =>
                "expected a single or double quote",
            MismatchedQuoteCharacters =>
                "mismatched quote character",
            ExpectedNumber =>
                "expected a number",
            ExpectedCurrentNode =>
                "Expected the current node token",
            ExpectedNamedOperator =>
                "expected a named operator",
            ExpectedAxis =>
                "expected an axis name",
            ExpectedAxisSeparator =>
                "expected an axis separator",
            ExpectedNodeTest =>
                "expected a node test",
            ExpectedQName =>
                "expected an optionally prefixed name",
            ExpectedNameTest =>
                "expected a name test",
            ExpectedVariableReference =>
                "expected a variable reference",
            ExpectedToken =>
                "expected a token",
            ExpectedLeftParenthesis =>
                "expected a left parenthesis",
            UnableToCreateToken =>
                "unable to create token",
        }
    }
}

impl fmt::Display for LexerError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        error::Error::description(self).fmt(fmt)
    }
}

use self::LexerError::*;

//============================================================================//
// Lexer type:
//============================================================================//

type In<'a>   = &'a str;
type Tok<'a>  = Token<In<'a>>;
type OIn<'a>  = Option<In<'a>>;
type OTok<'a> = Option<Tok<'a>>;

pub type LexResult<'a> = Result<Tok<'a>, LexerError>;

pub struct Lexer<'a> {
    remains: In<'a>,
    prefer_op_names: bool,
}

//============================================================================//
// Lexing macros:
//============================================================================//

macro_rules! vtag {
    ($i: expr, $v: expr, $t: expr) => ( value!($i, $v, tag!($t)) );
}

macro_rules! lerr {
    ($i: expr, $err: expr, $($args:tt)*) => (
        add_return_error!($i, ErrorKind::Custom($err),
            fix_error!(LexerError, $($args)*))
    );
}

macro_rules! rlerr {
    ($i: expr, $err: expr, $($args:tt)*) => (
        return_error!($i, ErrorKind::Custom($err),
            fix_error!(LexerError, $($args)*))
    );
}

macro_rules! par {
    ($name:ident, $t: ty, $($args:tt)*) => (
        named!($name(In) -> $t, $($args)*);
    );
}

macro_rules! lexer {
    ($name:ident, $err: expr, $($args:tt)*) => (
        lexer!($name, lerr!($err, $($args)*));
    );
    ($name:ident, $($args:tt)*) => (
        named!($name<In, Tok, LexerError>, $($args)*);
    );
}

//============================================================================//
// Const tokens:
//============================================================================//

static SINGLE_CHAR_TOKENS: phf::Map<In<'static>, CToken> = phf_map! {
    "/" => Slash,
    "(" => LeftParen,
    ")" => RightParen,
    "[" => LeftBracket,
    "]" => RightBracket,
    "@" => AtSign,
    "+" => PlusSign,
    "-" => MinusSign,
    "|" => Pipe,
    "=" => Equal,
    "<" => LessThan,
    ">" => GreaterThan,
    "," => Comma
};

static TWO_CHAR_TOKENS: phf::Map<In<'static>, CToken> = phf_map! {
    "<=" => LessThanOrEqual,
    ">=" => GreaterThanOrEqual,
    "!=" => NotEqual,
    "//" => DoubleSlash,
    ".." => ParentNode,
};

fn get_single(i: In) -> OTok<'static> {
    SINGLE_CHAR_TOKENS.get(i).cloned().map(Const)
}

fn get_two(i: In) -> OTok<'static> {
    TWO_CHAR_TOKENS.get(i).cloned().map(Const)
}

par!(star, In, tag!("*"));

lexer!(lex_single,       ExpectedToken,         map_opt!(take!(1), get_single));
lexer!(lex_two,          ExpectedToken,         map_opt!(take!(2), get_two));
lexer!(lex_current_node, ExpectedCurrentNode,   vtag!(Const(CurrentNode), "."));
lexer!(lex_named_op,     ExpectedNamedOperator, map!(
    alt_complete!(value!(Multiply, star)
                | vtag!(Or,        "or")
                | vtag!(And,       "and")
                | vtag!(Remainder, "mod")
                | vtag!(Divide,    "div")),
    Const
));

//============================================================================//
// Number:
//============================================================================//

/*
[30]    Number                          ::= Digits ('.' Digits?)? | '.' Digits
[31]    Digits                          ::= [0-9]+
*/
lexer!(lex_number, ExpectedNumber, map!(
    recognize!(alt!(terminated!(tag!("."), digit)
                  | terminated!(digit, opt!(terminated!(
                        complete!(tag!(".")),
                        opt!(complete!(digit))
                    )))
                )),
    |s: In| Number(s.parse().unwrap())
));

//============================================================================//
// Literal:
//============================================================================//

macro_rules! quoted_by {
    ($i: expr, $del: expr) => (
        preceded!($i,
            lerr!(ExpectedQuote, tag!($del)),
            rlerr!(MismatchedQuoteCharacters,
                   take_until_and_consume!($del)))
    )
}

//============================================================================//
// Axis specifier:
//============================================================================//

lexer!(lex_axis_spec, map!(terminated!(
    lerr!(ExpectedAxis, alt_complete!(
          vtag!(Child,            "child")
        | vtag!(Parent,           "parent")
        | vtag!(SelfAxis,         "self")
        | vtag!(Namespace,        "namespace")
        | vtag!(Attribute,        "attribute")
        | vtag!(AncestorOrSelf,   "ancestor-or-self")
        | vtag!(Ancestor,         "ancestor")
        | vtag!(DescendantOrSelf, "descendant-or-self")
        | vtag!(Descendant,       "descendant")
        | vtag!(FollowingSibling, "following-sibling")
        | vtag!(Following,        "following")
        | vtag!(PrecedingSibling, "preceding-sibling")
        | vtag!(Preceding,        "preceding"))),
    lerr!(ExpectedAxisSeparator, tag!("::"))), Axis
));

//============================================================================//
// Node type:
//============================================================================//

lexer!(lex_node_type, ExpectedNodeTest, map!(
    alt_complete!(vtag!(Text,    "text")
                | vtag!(Node,    "node")
                | vtag!(Comment, "comment")
                | vtag!(ProcIns, "processing-instruction")),
    NType
));

/*
//============================================================================//
// Name test:
//============================================================================//

NameStartChar  ::= [A-Z] | "_" | [a-z] | [#xC0-#xD6] | [#xD8-#xF6]
                 | [#xF8-#x2FF] | [#x370-#x37D] | [#x37F-#x1FFF]
                 | [#x200C-#x200D] | [#x2070-#x218F] | [#x2C00-#x2FEF]
                 | [#x3001-#xD7FF] | [#xF900-#xFDCF] | [#xFDF0-#xFFFD]
                 | [#x10000-#xEFFFF]
NameChar       ::= NameStartChar | "-" | "." | [0-9] | #xB7
                 | [#x0300-#x036F] | [#x203F-#x2040]
NCName         ::= NameStartChar (NameChar)*
*/

fn is_name_char_start(c: char) -> bool {
    match c {
          'A'         ... 'Z'
        | '_'         ... '_'
        | 'a'         ... 'z'
        | '\u{C0}'    ... '\u{D6}'
        | '\u{D8}'    ... '\u{F6}'
        | '\u{F8}'    ... '\u{2FF}'
        | '\u{370}'   ... '\u{37D}'
        | '\u{37F}'   ... '\u{1FFF}'
        | '\u{200C}'  ... '\u{200D}'
        | '\u{2070}'  ... '\u{218F}'
        | '\u{2C00}'  ... '\u{2FEF}'
        | '\u{3001}'  ... '\u{D7FF}'
        | '\u{F900}'  ... '\u{FDCF}'
        | '\u{FDF0}'  ... '\u{FFFD}'
        | '\u{10000}' ... '\u{EFFFF}' => true,
        _                             => false
    }
}

fn is_name_char(c: char) -> bool {
    is_name_char_start(c) ||
    match c {
          '-'        ... '-'
        | '.'        ... '.'
        | '0'        ... '9'
        | '\u{B7}'   ... '\u{B7}'
        | '\u{300}'  ... '\u{36F}'
        | '\u{203F}' ... '\u{2040}' => true,
        _                           => false
    }
}

fn name_char_start<'a>(i: In<'a>) -> IResult<In<'a>, In<'a>> {
    map_opt!(i, take!(1), |s: In<'a>|
        s.chars().next()
         .and_then(|c| if is_name_char_start(c) { Some(s) } else { None })
    )
}

par!(nc_name, In,
    recognize!(preceded!(name_char_start, take_while_s!(is_name_char)))
);
par!(prefix,     OIn, opt!(terminated!(nc_name, complete!(tag!(":")))));
par!(local_part, OIn, alt_complete!(value!(None, star) | map!(nc_name, Some)));

lexer!(lex_name_test, ExpectedNameTest, map!(
    pair!(prefix, local_part),
    |p| match p {
        (None,     None)     => Wildcard,
        (Some(ns), None)     => NSWildcard(ns),
        (None,     Some(lp)) => LocalPart(lp),
        (Some(ns), Some(lp)) => NSLocalPart(ns, lp),
    }
));
    //NTest(NameTest(ns, ln)))

//============================================================================//
// Function:
//============================================================================//

lexer!(lex_function, map!(
    terminated!(
        lerr!(ExpectedQName, qname),
        lerr!(ExpectedLeftParenthesis, complete!(peek!(tag!("("))))
    ),
    FnName
));

//============================================================================//
// VariableReference:
//============================================================================//

par!(qname, QName<In>, do_parse!(a: prefix >> b: nc_name >> (QName(a, b))));

lexer!(lex_varref, map!(
    preceded!(
        lerr!(ExpectedVariableReference, tag!("$")),
        lerr!(ExpectedQName, qname)
    ),
    VarRef
));

//============================================================================//
// All:
//============================================================================//

named!(whitespace<In, In, LexerError>, eat_separator!(" \t\r\n"));

fn lexer_tok(i: In, prefer_op_names: bool) -> IResult<In, Tok, LexerError> {
    #![allow(unused_variables)]
    delimited!(i,
        whitespace,
        alt!(alt_complete!(lex_two | lex_single)
           // lex_literal:
           | map!(alt!(quoted_by!("'") | quoted_by!("\"")), Literal)
           | alt_complete!(lex_number | lex_current_node)
           | cond_reduce!(prefer_op_names, lex_named_op)
           | lex_axis_spec
           | lex_node_type
           | lex_function
           | lex_name_test
           | lex_varref
        ),
        whitespace
    )
}

impl<'a> Lexer<'a> {
    pub fn new<'b>(src: In<'b>) -> Lexer<'b> {
        Lexer {
            remains: src,
            prefer_op_names: false
        }
    }

    pub fn is_finished(&self) -> bool {
        self.remains.is_empty()
    }

    fn next_token(&mut self) -> LexResult<'a> {
        match lexer_tok(self.remains, self.prefer_op_names) {
            Done(rem, tok) => {
                self.remains = rem;
                if tok.precedes_node_test()  ||
                   tok.precedes_expression() ||
                   tok.is_operator() {
                    self.prefer_op_names = false;
                } else {
                    // See http://www.w3.org/TR/xpath/#exprlex
                    self.prefer_op_names = true;
                }
                Ok(tok)
            },
            Error(ErrorKind::Custom(MismatchedQuoteCharacters))
                => Err(MismatchedQuoteCharacters),
            _   => Err(UnableToCreateToken)
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = LexResult<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.is_finished() { None } else { Some(self.next_token()) }
    }
}

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

    fn expand<'a>(&mut self, tok: Tok<'a>) -> Tok<'a> {
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

    type VTok<'a> = Vec<Tok<'a>>;

    use std::fmt::Debug;
    fn no_complete<T: Debug>(x: T) -> ! {
        panic!("parser did not complete, because:\n{:?}\n", x);
    }

    fn all_tokens_raw(i: In) -> Result<VTok, LexerError> {
        Lexer::new(i).collect()
    }

    fn all_tokens(i: In) -> VTok {
        all_tokens_raw(i).unwrap_or_else(|e| no_complete(e))
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

    fn lpar() -> Tok<'static> {
        Const(LeftParen)
    }

    fn rpar() -> Tok<'static> {
        Const(RightParen)
    }

    fn pars<'a>(first: Tok<'a>, args: VTok<'a>) -> VTok<'a> {
        let mut cont = vec![first, lpar()];
        cont.extend(args);
        cont.push(rpar());
        cont
    }

    /*
    fn ntest<'a>(ns: OIn<'a>, lp: OIn<'a>) -> Tok<'a> {
        NTest(NameTest(ns, lp))
    }
    */

    fn lp(lp: In) -> Tok {
        LocalPart(lp)
        //ntest(None, Some(lp))
    }

    fn q_lp<'a>(ns: In<'a>, lp: In<'a>) -> Tok<'a> {
        NSLocalPart(ns, lp)
        //ntest(Some(ns), Some(lp))
    }

    fn wc<'a>() -> Tok<'a> {
        Wildcard
        //ntest(None, None)
    }

    fn q_wc<'a>(ns: In<'a>) -> Tok<'a> {
        NSWildcard(ns)
        //ntest(Some(ns), None)
    }

    // Actual tests:

    tests! {
        (empty_string_has_no_tokens, "") => vec![],
        (ignores_whitespace_around_tokens, " @\t@\n@\r")
            => vec![Const(AtSign); 3]
    }

    mod consts {
        use super::*;
        fn c<'a>(ct: CToken) -> VTok<'a> { vec![Const(ct)] }
        tests! {
           // single
             (single_slash,  "/") => c(Slash)
           , (left_paren,    "(") => c(LeftParen)
           , (right_paren,   ")") => c(RightParen)
           , (left_bracket,  "[") => c(LeftBracket)
           , (right_bracket, "]") => c(RightBracket)
           , (at_sign,       "@") => c(AtSign)
           , (plus_sign,     "+") => c(PlusSign)
           , (minus_sign,    "-") => c(MinusSign)
           , (pipe,          "|") => c(Pipe)
           , (equal_sign,    "=") => c(Equal)
           , (less_than,     "<") => c(LessThan)
           , (greater_than,  ">") => c(GreaterThan)
           , (comma,         ">") => c(GreaterThan)
           // two
           , (lt_equal,     "<=") => c(LessThanOrEqual)
           , (gt_equal,     ">=") => c(GreaterThanOrEqual)
           , (neq_sign,     "!=") => c(NotEqual)
           , (double_slash, "//") => c(DoubleSlash)
           , (double_dot,   "..") => c(ParentNode)
           // special:
           , (single_dot,    ".") => c(CurrentNode)
        }
    }

    mod axis {
        use super::*;
        fn a<'a>(an: AxisName) -> VTok<'a> { vec![Axis(an)] }
        tests! {
              (axis_self,          "self::")               => a(SelfAxis)
            , (child,              "child::")              => a(Child)
            , (parent,             "parent::")             => a(Parent)
            , (namespace,          "namespace::")          => a(Namespace)
            , (attribute,          "attribute::")          => a(Attribute)
            , (ancestor,           "ancestor::")           => a(Ancestor)
            , (ancestor_or_self,   "ancestor-or-self::")   => a(AncestorOrSelf)
            , (following,          "following::")          => a(Following)
            , (following_sibling,  "following-sibling::")  => a(FollowingSibling)
            , (preceding,          "preceding::")          => a(Preceding)
            , (preceding_sibling,  "preceding-sibling::")  => a(PrecedingSibling)
            , (descendant,         "descendant::")         => a(Descendant)
            , (descendant_or_self, "descendant-or-self::") => a(DescendantOrSelf)
            , (ancestor_world, "ancestor::world")
                => vec![Axis(Ancestor), lp("world")]
            , (axis_that_contains_another_axis, "ancestor-or-self::world")
                => vec![Axis(AncestorOrSelf), lp("world")]
        }
    }

    mod number {
        use super::*;
        fn n<'a>(x: f64) -> VTok<'a> { vec![Number(x)] }
        tests! {
              (integral_number,                 "42")    => n(42.0)
            , (integral_number_dot,             "42.")   => n(42.0)
            , (decimal_number,                  "42.42") => n(42.42)
            , (decimal_number_no_integral_part, ".40")   => n(0.40)
        }
    }

    mod literal {
        use super::*;
        fn l<'a>(lit: In<'a>) -> VTok<'a> { vec![Literal(lit)] }
        tests! {
              (apostrophe_literal,   "'hello!'") => l("hello!")
            , (double_quote_literal, "\"1.23\"") => l("1.23")
        }
    }

    mod function {
        use super::*;

        fn fun<'a>(ns: OIn<'a>, lp: In<'a>, args: VTok<'a>) -> VTok<'a> {
            pars(FnName(QName(ns, lp)), args)
        }

        tests! {
            (call, "hello()") =>
                fun(None, "hello", vec![]),
            (call_with_argument, "hello(1)") =>
                fun(None, "hello", vec![Number(1.0)]),
            (call_with_multiple_arguments, "hello(1, 2)") =>
                fun(None, "hello", vec![Number(1.0), Const(Comma), Number(2.0)])
        }
    }

    mod node_type {
        use super::*;

        fn nt<'a>(nt: NodeType, args: VTok<'a>) -> VTok<'a> {
            pars(NType(nt), args)
        }

        tests! {
            (text, "text()")       => nt(Text, vec![]),
            (node, "node()")       => nt(Node, vec![]),
            (comment, "comment()") => nt(Comment, vec![]),
            (proc_ins_without_args, "processing-instruction()")
                => nt(ProcIns, vec![]),
            (proc_ins_with_args, "processing-instruction('hi')")
                => nt(ProcIns, vec![Literal("hi")])
        }
    }

    mod var_ref {
        use super::*;
        tests! {
            (local, "$yo")         => vec![VarRef(QName(None, "yo"))],
            (ns_local, "$abc:def") => vec![VarRef(QName(Some("abc"), "def"))]
        }
    }

    mod name_test {
        use super::*;
        tests! {
            (wildcard, "*")
                => vec![wc()],
            (ns_wildcard, "ns:*")
                => vec![q_wc("ns")],
            (qualified_name, "ns:foo")
                => vec![q_lp("ns", "foo")],
            (simple_string, "hello")
                => vec![lp("hello")],
            (spec_chars_1, "A0.bc:*")
                => vec![q_wc("A0.bc")],
            (spec_chars_2, "_01:A.5")
                => vec![q_lp("_01", "A.5")],
            (grandchild_selector, "hello/world")
                => vec![lp("hello"), Const(Slash), lp("world")],
            (great_grandchild_selector, "hello/there/world")
                => vec![lp("hello"), Const(Slash),
                        lp("there"), Const(Slash),
                        lp("world")],
            (double_slash_separator, "hello//world")
                => vec![lp("hello"), Const(DoubleSlash), lp("world")]
        }
    }

    mod special {
        use super::*;
        tests! {
            (preceding_token_forces_named_operator_and, "1andz2")
                => vec![Number(1.0), Const(And), lp("z2")],
            (preceding_token_forces_named_operator_or, "2oror")
                => vec![Number(2.0), Const(Or), lp("or")],
            (preceding_token_forces_named_operator_mod, "3moddiv")
                => vec![Number(3.0), Const(Remainder), lp("div")],
            (preceding_token_forces_named_operator_div, "1divz2")
                => vec![Number(1.0), Const(Divide), lp("z2")],
            (preceding_token_forces_named_operator_multiply, "1*2")
                => vec![Number(1.0), Const(Multiply), Number(2.0)]
        }
    }

    mod execption_thrown {
        use super::*;

        #[test]
        fn when_nothing_was_tokenized() {
            assert_eq!(all_tokens_raw("!"), Err(UnableToCreateToken));
        }

        #[test]
        fn when_name_test_has_no_local_name() {
            assert_eq!(all_tokens_raw("ns:"), Err(UnableToCreateToken));
        }

        #[test]
        fn when_quote_characters_mismatched() {
            assert_eq!(all_tokens_raw("'hello\""), Err(MismatchedQuoteCharacters));
        }
    }

    mod compound {
    }
}