//============================================================================//
// Imports:
//============================================================================//

use phf;

use nom::*;
use nom::IResult::*;

// tokens:
use super::tokens::*;
use super::tokens::CToken::*;
use super::tokens::AxisName::*;
use super::tokens::NodeType::*;
use super::tokens::Token::*;

use self::Error::*;

//============================================================================//
// Public API, Lexer errors:
//============================================================================//

quick_error! {
    /// Indicates that an error occurred in the lexing phase of parsing.
    #[derive(PartialEq, Debug, Clone)]
    pub enum Error {
        ExpectedQuote {
            description("expected a single or double quote")
        }
        MismatchedQuoteCharacters {
            description("mismatched quote character")
        }
        ExpectedNumber {
            description("expected a number")
        }
        ExpectedCurrentNode {
            description("expected the current node token")
        }
        ExpectedNamedOperator {
            description("expected a named operator")
        }
        ExpectedAxis {
            description("expected an axis name")
        }
        ExpectedAxisSeparator {
            description("expected an axis separator")
        }
        ExpectedNodeTest {
            description("expected a node test")
        }
        ExpectedQName {
            description("expected an optionally prefixed name")
        }
        ExpectedNameTest {
            description("expected a name test")
        }
        ExpectedVariableReference {
            description("expected a variable reference")
        }
        ExpectedToken {
            description("expected a token")
        }
        ExpectedLeftParenthesis {
            description("expected a left parenthesis")
        }
        UnableToCreateToken {
            description("unable to create token")
        }
    }
}

/// The result of running the lexer on some input.
pub type LexerResult<'a> = Result<StrToken<'a>, Error>;

//============================================================================//
// Public API, Lexer type:
//============================================================================//

/// A [`Token`], with `&'a str` as the backing type for strings.
///
/// [`Token`]: struct.Token.html
pub(crate) type StrToken<'a> = Token<In<'a>>;

/// The lexer of xpath expressions.
pub struct Lexer<'a> {
    remains: In<'a>,
    prefer_op_names: bool,
}

//============================================================================//
// Public API, Lexer implementation:
//============================================================================//

impl<'a> Lexer<'a> {
    /// Constructs a new lexer for the given input string slice.
    pub fn new(src: In) -> Lexer {
        Lexer {
            remains: src,
            prefer_op_names: false,
        }
    }

    /// Yields true if nothing remains to be lexed.
    pub fn is_finished(&self) -> bool {
        self.remains.is_empty()
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = LexerResult<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.is_finished() {
            None
        } else {
            Some(self.next_token())
        }
    }
}

//============================================================================//
// Internally used types:
//============================================================================//

// Various type aliases for brevity.

/// Input type for all lexing.
type In<'a> = &'a str;

/// Option variant of input type.
type OIn<'a> = Option<In<'a>>;

/// Optional Token for &str.
type OTok<'a> = Option<StrToken<'a>>;

//============================================================================//
// Lexing macros:
//============================================================================//

/// Produce the first argument if the second matches.
macro_rules! vtag {
    ($i: expr, $v: expr, $t: expr) => ( value!($i, $v, tag!($t)) );
}

/// Fixes the error to the variant of `Error` specified.
macro_rules! lerr {
    ($i: expr, $err: expr, $($args:tt)*) => (
        add_return_error!($i, ErrorKind::Custom($err),
            fix_error!(Error, $($args)*))
    );
}

/// Prevents backtracking in the child parser and fixes the error
/// to the variant of `Error` specified.
macro_rules! rlerr {
    ($i: expr, $err: expr, $($args:tt)*) => (
        return_error!($i, ErrorKind::Custom($err),
            fix_error!(Error, $($args)*))
    );
}

/// Creates a named parser with input type `In` and output type according
/// to the second argument.
macro_rules! par {
    ($name:ident, $t: ty, $($args:tt)*) => (
        named!($name(In) -> $t, $($args)*);
    );
}

/// Creates a lexer for an entire category.
/// It is named as the first argument with potential
/// error specified in the second argument.
macro_rules! lexer {
    ($name:ident, $err: expr, $($args:tt)*) => (
        lexer!($name, lerr!($err, $($args)*));
    );
    ($name:ident, $($args:tt)*) => (
        named!($name<In, StrToken, Error>, $($args)*);
    );
}

//============================================================================//
// Const tokens:
//============================================================================//

/// A map of all single character tokens.
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

// A map of all two character tokens.
static TWO_CHAR_TOKENS: phf::Map<In<'static>, CToken> = phf_map! {
    "<=" => LessThanOrEqual,
    ">=" => GreaterThanOrEqual,
    "!=" => NotEqual,
    "//" => DoubleSlash,
    ".." => ParentNode,
};

/// Matches the input against any symbol in `SINGLE_CHAR_TOKENS`.
fn get_single(i: In) -> OTok<'static> {
    SINGLE_CHAR_TOKENS.get(i).cloned().map(Const)
}

/// Matches the input against any symbol in `TWO_CHAR_TOKENS`.
fn get_two(i: In) -> OTok<'static> {
    TWO_CHAR_TOKENS.get(i).cloned().map(Const)
}

/// A lexer matching a star (*) symbol.
par!(star, In, tag!("*"));

/// A lexer matching a single character token.
lexer!(lex_single, ExpectedToken, map_opt!(take!(1), get_single));

/// A lexer matching a two character token.
lexer!(lex_two, ExpectedToken, map_opt!(take!(2), get_two));

/// A lexer matching a dot (.) symbol and producing a `CurrentNode` token.
lexer!(
    lex_current_node,
    ExpectedCurrentNode,
    vtag!(Const(CurrentNode), ".")
);

/// A lexer matching any of
/// { "or" => Or, "and" => And, "mod" => Remainder, "div" => Divide }.
lexer!(
    lex_named_op,
    ExpectedNamedOperator,
    map!(
        alt_complete!(
            value!(Multiply, star) | vtag!(Or, "or") | vtag!(And, "and") |
                vtag!(Remainder, "mod") | vtag!(Divide, "div")
        ),
        Const
    )
);

//============================================================================//
// Number:
//============================================================================//

/*
[30]    Number                          ::= Digits ('.' Digits?)? | '.' Digits
[31]    Digits                          ::= [0-9]+
*/
/// A lexer matching a number (both integer and floating point).
lexer!(
    lex_number,
    ExpectedNumber,
    map!(
        recognize!(alt!(
            terminated!(tag!("."), digit) |
                terminated!(
                    digit,
                    opt!(terminated!(complete!(tag!(".")), opt!(complete!(digit))))
                )
        )),
        // We are certain at this point that it will parse into a number,
        // therefore it is safe to .unwrap().
        |s: In| Number(s.parse().unwrap())
    )
);

//============================================================================//
// Literal:
//============================================================================//

/// A lexer matching a quoted literal string.
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

/// A lexer matching any axis specifier followed by "::".
lexer!(
    lex_axis_spec,
    map!(
        terminated!(
            lerr!(
                ExpectedAxis,
                alt_complete!(
                    vtag!(Child, "child") | vtag!(Parent, "parent") | vtag!(SelfAxis, "self") |
                        vtag!(Namespace, "namespace") |
                        vtag!(Attribute, "attribute") |
                        vtag!(AncestorOrSelf, "ancestor-or-self") |
                        vtag!(Ancestor, "ancestor") |
                        vtag!(DescendantOrSelf, "descendant-or-self") |
                        vtag!(Descendant, "descendant") |
                        vtag!(FollowingSibling, "following-sibling") |
                        vtag!(Following, "following") |
                        vtag!(PrecedingSibling, "preceding-sibling") |
                        vtag!(Preceding, "preceding")
                )
            ),
            lerr!(ExpectedAxisSeparator, tag!("::"))
        ),
        Axis
    )
);

//============================================================================//
// Node type:
//============================================================================//

// A lexer matching any node type.
lexer!(
    lex_node_type,
    ExpectedNodeTest,
    map!(
        alt_complete!(
            vtag!(Text, "text") | vtag!(Node, "node") | vtag!(Comment, "comment") |
                vtag!(ProcIns, "processing-instruction")
        ),
        NType
    )
);

//============================================================================//
// Name test:
//============================================================================//

/*
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
        'A'...'Z' |
        '_'...'_' |
        'a'...'z' |
        '\u{C0}'...'\u{D6}' |
        '\u{D8}'...'\u{F6}' |
        '\u{F8}'...'\u{2FF}' |
        '\u{370}'...'\u{37D}' |
        '\u{37F}'...'\u{1FFF}' |
        '\u{200C}'...'\u{200D}' |
        '\u{2070}'...'\u{218F}' |
        '\u{2C00}'...'\u{2FEF}' |
        '\u{3001}'...'\u{D7FF}' |
        '\u{F900}'...'\u{FDCF}' |
        '\u{FDF0}'...'\u{FFFD}' |
        '\u{10000}'...'\u{EFFFF}' => true,
        _ => false,
    }
}

fn is_name_char(c: char) -> bool {
    is_name_char_start(c) || match c {
        '-'...'-' |
        '.'...'.' |
        '0'...'9' |
        '\u{B7}'...'\u{B7}' |
        '\u{300}'...'\u{36F}' |
        '\u{203F}'...'\u{2040}' => true,
        _ => false,
    }
}

fn name_char_start<'a>(i: In<'a>) -> IResult<In<'a>, In<'a>> {
    map_opt!(i, take!(1), |s: In<'a>| {
        s.chars()
            .next()
            .and_then(|c| if is_name_char_start(c) { Some(s) } else { None })
    })
}

/// A lexer matching an NCName.
par!(
    nc_name,
    In,
    recognize!(preceded!(name_char_start, take_while_s!(is_name_char)))
);

/// A lexer matching a prefix.
par!(
    prefix,
    OIn,
    opt!(terminated!(nc_name, complete!(tag!(":"))))
);

/// A lexer matching a local part.
par!(
    local_part,
    OIn,
    alt_complete!(value!(None, star) | map!(nc_name, Some))
);

/// A lexer matching a name test.
lexer!(
    lex_name_test,
    ExpectedNameTest,
    map!(
        pair!(prefix, local_part),
        |(ns, lp)| NTest(NameTest(ns, lp))
    )
);

//============================================================================//
// Function:
//============================================================================//

/// A lexer matching a function name.
lexer!(
    lex_function,
    map!(
        terminated!(
            lerr!(ExpectedQName, qname),
            lerr!(ExpectedLeftParenthesis, complete!(peek!(tag!("("))))
        ),
        FnName
    )
);

//============================================================================//
// VariableReference:
//============================================================================//

/// A lexer matching a QName.
par!(qname, QName<In>, do_parse!(a: prefix >> b: nc_name >> (QName(a, b))));

// A lexer matching a variable reference.
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

named!(whitespace<In, In, Error>, eat_separator!(" \t\r\n"));

/// Lexes a single token given input and whether to prefer operator names or not.
fn lexer_tok(i: In, prefer_op_names: bool) -> IResult<In, StrToken, Error> {
    #![allow(unused_variables)]
    #![allow(unknown_lints)]
    #![allow(cyclomatic_complexity)]
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
    /// Produces the next available lexeme / token, if any,
    /// and advances the remaining input.
    fn next_token(&mut self) -> LexerResult<'a> {
        match lexer_tok(self.remains, self.prefer_op_names) {
            Done(rem, tok) => {
                self.remains = rem;
                // See http://www.w3.org/TR/xpath/#exprlex
                self.prefer_op_names =
                    !(tok.precedes_node_test() || tok.precedes_expression() || tok.is_operator());
                Ok(tok)
            }
            Error(ErrorKind::Custom(MismatchedQuoteCharacters)) => Err(MismatchedQuoteCharacters),
            _ => Err(UnableToCreateToken),
        }
    }
}

//============================================================================//
// Tests:
//============================================================================//

#[cfg(test)]
mod tests {
    use super::*;
    use super::Error;

    // helpers & macros:

    type VTok<'a> = Vec<StrToken<'a>>;

    use std::fmt::Debug;
    fn no_complete<T: Debug>(x: T) -> ! {
        panic!("parser did not complete, because:\n{:?}\n", x);
    }

    /// Lexes the input completely into a vector.
    fn all_tokens_raw(i: In) -> Result<VTok, Error> {
        Lexer::new(i).collect()
    }

    /// Lexes the input completely and ensures the lexer did not error.
    fn all_tokens(i: In) -> VTok {
        all_tokens_raw(i).unwrap_or_else(|e| no_complete(e))
    }

    /// Macro for writing lexer tests.
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

    fn lpar() -> StrToken<'static> {
        Const(LeftParen)
    }

    fn rpar() -> StrToken<'static> {
        Const(RightParen)
    }

    /// Fuses together a token and subsequent vector of tokens into a vector.
    fn pars<'a>(first: StrToken<'a>, args: VTok<'a>) -> VTok<'a> {
        let mut cont = vec![first, lpar()];
        cont.extend(args);
        cont.push(rpar());
        cont
    }

    /// Creates a NameTest token out of the namespace/prefix and local part.
    fn ntest<'a>(ns: OIn<'a>, lp: OIn<'a>) -> StrToken<'a> {
        NTest(NameTest(ns, lp))
    }

    fn lp(lp: In) -> StrToken {
        ntest(None, Some(lp))
    }

    fn q_lp<'a>(ns: In<'a>, lp: In<'a>) -> StrToken<'a> {
        ntest(Some(ns), Some(lp))
    }

    fn wc<'a>() -> StrToken<'a> {
        ntest(None, None)
    }

    fn q_wc<'a>(ns: In<'a>) -> StrToken<'a> {
        ntest(Some(ns), None)
    }

    //============================================================================//
    // Actual tests:
    //============================================================================//

    tests! {
        (empty_string_has_no_tokens, "") => vec![],
        (ignores_whitespace_around_tokens, " @\t@\n@\r")
            => vec![Const(AtSign); 3]
    }

    /// Tests for the Const producing lexers.
    mod consts {
        use super::*;
        fn c<'a>(ct: CToken) -> VTok<'a> {
            vec![Const(ct)]
        }
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

    /// Tests for the axis lexer.
    mod axis {
        use super::*;
        fn a<'a>(an: AxisName) -> VTok<'a> {
            vec![Axis(an)]
        }
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

    /// Test for the the number lexer.
    mod number {
        use super::*;
        fn n<'a>(x: f64) -> VTok<'a> {
            vec![Number(x)]
        }
        tests! {
              (integral_number,                 "42")    => n(42.0)
            , (integral_number_dot,             "42.")   => n(42.0)
            , (decimal_number,                  "42.42") => n(42.42)
            , (decimal_number_no_integral_part, ".40")   => n(0.40)
        }
    }

    /// Tests for the string literal lexer.
    mod literal {
        use super::*;
        fn l<'a>(lit: In<'a>) -> VTok<'a> {
            vec![Literal(lit)]
        }
        tests! {
              (apostrophe_literal,   "'hello!'") => l("hello!")
            , (double_quote_literal, "\"1.23\"") => l("1.23")
        }
    }

    /// Tests for the function application lexer.
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

    /// Tests for the node type lexer.
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

    /// Tests for the variable reference lexer.
    mod var_ref {
        use super::*;
        tests! {
            (local, "$yo")         => vec![VarRef(QName(None, "yo"))],
            (ns_local, "$abc:def") => vec![VarRef(QName(Some("abc"), "def"))]
        }
    }

    /// Tests for the name test lexer.
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

    /// Tests for the special rules of the lexer when it comes to operators.
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

    /// Tests for ensuring that error are produces in certain cases.
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

    mod compound {}
}
