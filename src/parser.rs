//============================================================================//
// Imports:
//============================================================================//

use unreachable::unreachable;

use std::iter::Peekable;

use super::expr;
use super::expr::*;
use super::tokens;
use super::tokens::*;
use super::tokens::CToken::*;
use super::lexer::{self, LexerResult, StrToken};
use super::util::to_boxed_str;

use self::Error::*;

//============================================================================//
// Errors:
//============================================================================//

quick_error! {
    /// Possible error variants during XPath parsing.
    #[derive(Debug, Clone, PartialEq)]
    pub enum Error {
        EmptyPredicate {
            description("empty predicate")
        }
        ExtraUnparsedTokens {
            description("extra unparsed tokens")
        }
        RanOutOfInput {
            description("ran out of input")
        }
        RightHandSideExpressionMissing {
            description("right hand side of expression is missing")
        }
        ArgumentMissing {
            description("function argument is missing")
        }
        Lexer(err: lexer::Error) {
            from()
            cause(err)
            description(err.description())
            display("lexer error: {}", err)
        }
        TrailingSlash {
            description("trailing slash")
        }
        UnexpectedToken(token: Token<Box<str>>) {
            from()
            description("unexpected token")
            display("unexpected token: {:?}", token)
        }
        EmptyXPath {
            description("XPath was empty")
        }
    }
}

impl<'a> From<StrToken<'a>> for Error {
    fn from(t: StrToken<'a>) -> Self {
        t.boxed_str().into()
    }
}

//============================================================================//
// Parser API:
//============================================================================//

/// The result of running the lexer on some input.
pub type ParseResult<T> = Result<T, Error>;

/// An `XPath` expression parser.
struct Parser;

impl Parser {
    /// Constructs a new parser.
    pub fn new() -> Self {
        Parser
    }
}

impl Default for Parser {
    fn default() -> Self {
        Parser
    }
}

impl Parser {
    pub fn parse<'a, I>(&self, source: I) -> ParseResult<Expr>
    where
        I: Iterator<Item = LexerResult<'a>>,
    {
        let mut source = source.peekable();

        let expr = parse_or_expression(&mut source)?;

        if source.has_more_tokens() {
            return Err(ExtraUnparsedTokens);
        }
        
        expr.ok_or(EmptyXPath)
    }
}

//============================================================================//
// Internal: Types:
//============================================================================//

type OExpr = Option<Expr>;

type TokenSource<'a, I> = &'a mut Peekable<I>;

type Rule<'a, I> = Fn(TokenSource<I>) -> ParseResult<OExpr>;

type BinaryExpressionBuilder = fn(BExpr, BExpr) -> Expr;

struct BinaryRule {
    token: CToken,
    builder: BinaryExpressionBuilder,
}

//============================================================================//
// Internal: Binary operator constructors:
//============================================================================//

macro_rules! new_bin_op {
    ($fn: ident, $op: expr) => {
        fn $fn(l: BExpr, r: BExpr) -> Expr {
            Expr::Bin($op, l, r)
        }
    }
}

new_bin_op!(new_or, BinaryOp::Or);
new_bin_op!(new_and, BinaryOp::And);
new_bin_op!(new_eq, BinaryOp::Eq);
new_bin_op!(new_neq, BinaryOp::NEq);
new_bin_op!(new_lt, BinaryOp::Lt);
new_bin_op!(new_le, BinaryOp::LEq);
new_bin_op!(new_gt, BinaryOp::Gt);
new_bin_op!(new_ge, BinaryOp::GEq);
new_bin_op!(new_add, BinaryOp::Add);
new_bin_op!(new_sub, BinaryOp::Sub);
new_bin_op!(new_mul, BinaryOp::Mul);
new_bin_op!(new_div, BinaryOp::Div);
new_bin_op!(new_rem, BinaryOp::Rem);
new_bin_op!(new_union, BinaryOp::Union);

//============================================================================//
// Internal: Conversions:
//============================================================================//

fn conv_qname(qname: tokens::QName<&str>) -> expr::QName {
    let bname = qname.boxed_str();
    expr::QName(bname.0, bname.1)
}

fn conv_name_test(nt: tokens::NameTest<&str>) -> expr::NameTest {
    let bnt = nt.boxed_str();
    expr::NameTest {
        prefix: bnt.0,
        local: bnt.1,
    }
}

//============================================================================//
// Internal: Parsing utilities:
//============================================================================//

trait XCompat<'a> {
    fn has_more_tokens(&mut self) -> bool;
    fn next_token_is(&mut self, token: CToken) -> bool;
    fn consume(&mut self, token: CToken) -> ParseResult<()>;
    fn consume_if_eq(&mut self, token: CToken) -> bool;
}

impl<'a, I> XCompat<'a> for Peekable<I>
where
    I: Iterator<Item = LexerResult<'a>>,
{
    fn has_more_tokens(&mut self) -> bool {
        self.peek().is_some()
    }

    fn next_token_is(&mut self, token: CToken) -> bool {
        match self.peek() {
            Some(&Ok(ref t)) => t == &Token::Const(token),
            _ => false,
        }
    }

    fn consume(&mut self, token: CToken) -> ParseResult<()> {
        match self.next() {
            None => Err(RanOutOfInput),
            Some(Err(x)) => Err(Lexer(x)),
            Some(Ok(x)) => if x == Token::Const(token) {
                Ok(())
            } else {
                Err(x.into())
            },
        }
    }

    fn consume_if_eq(&mut self, token: CToken) -> bool {
        let r = self.next_token_is(token);
        if r {
            self.next();
        }
        r
    }
}

macro_rules! basic_parser {
    ($name: ident ($source: ident $(, [$($mut:tt)*] $par: ident : $tpar: ty)*) -> $tret: ty { $($args:tt)* }) => {
        fn $name<'a, I>($source: TokenSource<I> $(, $($mut)* $par : $tpar)*) -> $tret
        where I: Iterator<Item = LexerResult<'a>>,
        {
            $($args)*
        }
    }
}

macro_rules! parser {
    ($name: ident ($source: ident $(, [$($mut:tt)*] $par: ident : $tpar: ty)*) -> $tret: ty { $($args:tt)* }) => {
        fn $name<'a, I>($source: TokenSource<I> $(, $($mut)* $par : $tpar)*) -> ParseResult<$tret>
        where I: Iterator<Item = LexerResult<'a>>,
        {
            $($args)*
        }
    }
}

parser!(lassoc_parse(i,
    [] child_parse: fn(TokenSource<I>) -> ParseResult<OExpr>,
    [] rules: &[BinaryRule]) -> OExpr {
    let mut left = if let Some(x) = child_parse(i)? { x }
                   else { return Ok(None) };

    #[allow(never_loop)]
    'outer: while i.has_more_tokens() {
        for rule in rules {
            if i.consume_if_eq(rule.token) {
                let right = if let Some(x) = child_parse(i)? { x }
                            else { return Err(RightHandSideExpressionMissing) };

                left = (rule.builder)(Box::new(left), Box::new(right));
                continue 'outer;
            }
        }

        break 'outer;
    }

    Ok(Some(left))
});

parser!(first_matching_rule(i, [] sub_parsers: &[&Rule<I>]) -> OExpr {
    for sub in sub_parsers.iter() {
        let expr = (*sub)(i)?;
        if expr.is_some() {
            return Ok(expr);
        }
    }

    Ok(None)
});

basic_parser!(consume_slash(i) -> bool {
    i.consume_if_eq(Slash)
});

macro_rules! consume_match(
    ($source:expr, Token::$token:ident) => (
        if let Some(&Ok(Token::$token(_))) = $source.peek() {
            if let Some(Ok(Token::$token(x))) = $source.next() { Some(x) }
            else { unsafe { unreachable() } }
        } else { None }
    );
);

fn delim_par<'a, I, F, T>(source: TokenSource<I>, interior: F) -> ParseResult<T>
where
    I: Iterator<Item = LexerResult<'a>>,
    F: FnOnce(TokenSource<I>) -> ParseResult<T>,
{
    source.consume(LeftParen)?;
    let ret = interior(source)?;
    source.consume(RightParen)?;
    Ok(ret)
}

fn brule(ct: CToken, b: BinaryExpressionBuilder) -> BinaryRule {
    BinaryRule {
        token: ct,
        builder: b,
    }
}

//============================================================================//
// Internal: Parsers:
//============================================================================//

parser!(parse_expression(i) -> OExpr { parse_or_expression(i) });

parser!(parse_or_expression(i) -> OExpr {
    lassoc_parse(i, parse_and_expression, &[brule(Or, new_or)])
});

parser!(parse_and_expression(i) -> OExpr {
    lassoc_parse(i, parse_equality_expression, &[brule(And, new_and)])
});

parser!(parse_equality_expression(i) -> OExpr {
    lassoc_parse(i, parse_relational_expression, &[
        brule(Equal, new_eq),
        brule(NotEqual, new_neq),
    ])
});

parser!(parse_relational_expression(i) -> OExpr {
    lassoc_parse(i, parse_additive_expression, &[
        brule(LessThan, new_lt),
        brule(LessThanOrEqual, new_le),
        brule(GreaterThan, new_gt),
        brule(GreaterThanOrEqual, new_ge),
    ])
});

parser!(parse_additive_expression(i) -> OExpr {
    lassoc_parse(i, parse_multiplicative_expression, &[
        brule(PlusSign, new_add),
        brule(MinusSign, new_sub),
    ])
});

parser!(parse_multiplicative_expression(i) -> OExpr {
    lassoc_parse(i, parse_unary_expression, &[
        brule(Multiply, new_mul),
        brule(Divide, new_div),
        brule(Remainder, new_rem),
    ])
});

parser!(parse_unary_expression(i) -> OExpr {
    let expr = parse_union_expression(i)?;
    if expr.is_some() {
        return Ok(expr);
    }

    i.consume_if_eq(MinusSign).failible_map(|_|
        parse_unary_expression(i)?.map_or_else(
            || Err(RightHandSideExpressionMissing),
            |e| Ok(Some(Expr::Neg(Box::new(e)))),
        )
    )
});

parser!(parse_union_expression(i) -> OExpr {
    lassoc_parse(i, parse_path_expression, &[brule(Pipe, new_union)])
});

parser!(parse_path_expression(i) -> OExpr {
    let expr = parse_location_path(i)?;
    if expr.is_some() {
        return Ok(expr);
    } // TODO: investigate if this is a pattern

    parse_filter_expression(i)?.failible_map(|expr| {
        if consume_slash(i) {
            parse_relative_location_path_raw(i, expr)?
                .map_or_else(|| Err(TrailingSlash), |e| Ok(Some(e)))
        } else {
            Ok(Some(expr))
        }
    })
});

parser!(parse_filter_expression(i) -> OExpr {
    parse_primary_expression(i)?.failible_map(|expr| {
        Ok(Some(parse_predicates(i)?.into_iter().fold(
            expr,
            |expr, pred| Expr::Filter(Box::new(expr), Box::new(pred)),
        )))
    })
});

parser!(parse_location_path(i) -> OExpr {
    first_matching_rule(i, &[
        &|s| parse_relative_location_path(s),
        &|s| parse_absolute_location_path(s),
    ])
});

parser!(parse_absolute_location_path(i) -> OExpr {
    consume_slash(i).failible_map(|_|
        parse_relative_location_path_raw(i, Expr::RootNode)
            .map(|path| path.or_else(|| Some(Expr::RootNode))))
});

parser!(parse_relative_location_path(i) -> OExpr {
    parse_relative_location_path_raw(i, Expr::ContextNode)
});

parser!(parse_relative_location_path_raw(i, [] start_point: Expr) -> OExpr {
    parse_step(i)?.failible_map(|step| {
        let mut steps = vec![step];
        while consume_slash(i) {
            if let Some(next) = parse_step(i)? { steps.push(next) }
            else { return Err(TrailingSlash) }
        }

        Ok(Some(Expr::Path(Box::new(start_point), steps.into_boxed_slice())))
    })
});

parser!(parse_step(i) -> Option<Steps> {
    let axis = parse_axis(i)?;

    let node_test = if let Some(test) = parse_node_test(i)? { Some(test) }
                    else { default_node_test(i, axis)? };

    node_test.failible_map(|nt| parse_predicates(i).map(|predicates|
        Some(Steps::new(axis, nt, predicates.into_boxed_slice()))
    ))
});

parser!(parse_predicates(i) -> Vec<Expr> {
    let mut predicates = Vec::new();
    while let Some(predicate) = parse_predicate_expression(i)? {
        predicates.push(predicate)
    }
    Ok(predicates)
});

parser!(parse_predicate_expression(i) -> OExpr {
    i.consume_if_eq(LeftBracket).failible_map(|_| {
        parse_expression(i)?.map_or_else(|| Err(EmptyPredicate), |predicate| {
            i.consume(RightBracket)?;
            Ok(Some(predicate))
        })
    })
});

parser!(parse_primary_expression(i) -> OExpr {
    first_matching_rule(i, &[
        &|s| parse_variable_reference(s),
        &|s| parse_nested_expression(s),
        &|s| parse_string_literal(s),
        &|s| parse_numeric_literal(s),
        &|s| parse_function_call(s),
    ])
});

parser!(parse_function_call(i) -> OExpr {
    consume_match!(i, Token::FnName).failible_map(|name|
        delim_par(i, parse_function_args).map(Vec::into_boxed_slice)
            .map(|arguments| Some(Expr::Apply(conv_qname(name), arguments))))
});

parser!(parse_function_args(i) -> Vec<Expr> {
    let mut arguments = Vec::new();

    if let Some(arg) = parse_expression(i)? { arguments.push(arg) }
    else { return Ok(arguments) }

    parse_function_args_tail(i, arguments)
});

parser!(parse_function_args_tail(i, [mut] arguments: Vec<Expr>) -> Vec<Expr> {
    while i.consume_if_eq(Comma) {
        if let Some(arg) = parse_expression(i)? { arguments.push(arg) }
        else { return Err(ArgumentMissing) }
    }

    Ok(arguments)
});

parser!(parse_numeric_literal(i) -> OExpr {
    Ok(consume_match!(i, Token::Number).map(From::from))
});

basic_parser!(parse_str(i) -> Option<Box<str>> {
    consume_match!(i, Token::Literal).map(to_boxed_str)
});

parser!(parse_string_literal(i) -> OExpr {
    Ok(parse_str(i).map(LiteralValue::String).map(Expr::Literal))
});

parser!(parse_variable_reference(i) -> OExpr {
    Ok(consume_match!(i, Token::VarRef).map(conv_qname).map(Expr::Var))
});

parser!(parse_nested_expression(i) -> OExpr {
    if i.next_token_is(LeftParen) {
        delim_par(i, parse_expression)
    } else { Ok(None) }
});

parser!(default_node_test(i, [] axis: Axis) -> Option<NodeTest> {
    Ok(consume_match!(i, Token::NTest).map(conv_name_test).map(|name|
        match axis.principal_node_type() {
            PrincipalNodeType::Attribute => NodeTest::Attribute(name),
            PrincipalNodeType::Element => NodeTest::Element(name),
            PrincipalNodeType::Namespace => NodeTest::Namespace(name),
    }))
});

parser!(parse_node_test(i) -> Option<NodeTest> {
    consume_match!(i, Token::NType).failible_map(|name| {
        delim_par(i, |i| Ok(Some(match name {
            NodeType::Text => NodeTest::Text,
            NodeType::Node => NodeTest::Node,
            NodeType::Comment => NodeTest::Comment,
            NodeType::ProcIns => NodeTest::ProcIns(parse_str(i))
        })))
    })
});

parser!(parse_axis(i) -> Axis {
    Ok(consume_match!(i, Token::Axis).map_or_else(|| Axis::Child, |ax| match ax {
        AxisName::Child => Axis::Child,
        AxisName::SelfAxis => Axis::SelfAxis,
        AxisName::Parent => Axis::Parent,
        AxisName::Descendant => Axis::Descendant,
        AxisName::DescendantOrSelf => Axis::DescendantOrSelf,
        AxisName::Attribute => Axis::Attribute,
        AxisName::Namespace => Axis::Namespace,
        AxisName::Ancestor => Axis::Ancestor,
        AxisName::AncestorOrSelf => Axis::AncestorOrSelf,
        AxisName::PrecedingSibling => Axis::PrecedingSibling,
        AxisName::FollowingSibling => Axis::FollowingSibling,
        AxisName::Preceding => Axis::Preceding,
        AxisName::Following => Axis::Following,
    }))
});

trait FailibleMap<T> {
    fn failible_map<F, U, E>(self, F) -> Result<Option<U>, E>
    where
        F: FnOnce(T) -> Result<Option<U>, E>;
}

impl<T> FailibleMap<T> for Option<T> {
    fn failible_map<F, U, E>(self, cont: F) -> Result<Option<U>, E>
    where
        F: FnOnce(T) -> Result<Option<U>, E>,
    {
        self.map_or_else(|| Ok(None), cont)
    }
}

impl FailibleMap<()> for bool {
    fn failible_map<F, U, E>(self, cont: F) -> Result<Option<U>, E>
    where
        F: FnOnce(()) -> Result<Option<U>, E>,
    {
        if self { cont(()) } else { Ok(None) }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use lexer::Error::*;
    use tokens::Token::*;
    //use super::Error::*;

    fn name_test<S: AsRef<str>>(s: S) -> Token<S> {
        NTest(s.into())
    }

    macro_rules! tokens(
        ($($e:expr),*) => ({
            let mut _temp: Vec<LexerResult> = Vec::new();
            $(_temp.push(Ok($e));)*
            _temp
        });
        ($($e:expr),+,) => (tokens!($($e),+))
    );

    fn parse_raw<'a, I>(input: I) -> ParseResult<Expr>
    where
        I: IntoIterator<Item = LexerResult<'a>>,
    {
        Parser::new().parse(input.into_iter())
    }

    macro_rules! assert_err {
        ($err: expr, $res: expr) => {
            assert_eq!(Err($err), $res);
        }
    }

    macro_rules! expect_parse_error {
        ($err: expr, $tokens: expr) => {
            assert_err!($err, parse_raw($tokens));
        }
    }

    // TODO

    #[test]
    fn unexpected_token_is_reported_as_an_error() {
        expect_parse_error!(UnexpectedToken(Const(RightParen)), tokens![
            FnName("does-not-matter".into()),
            Const(RightParen)
        ]);
    }

    #[test]
    fn binary_operator_without_right_hand_side_is_reported_as_an_error() {
        expect_parse_error!(RightHandSideExpressionMissing, tokens![
            Literal("left"),
            Const(And)
        ]);
    }

    #[test]
    fn unary_operator_without_right_hand_side_is_reported_as_an_error() {
        expect_parse_error!(RightHandSideExpressionMissing, tokens![
            Const(MinusSign),
        ]);
    }

    #[test]
    fn empty_predicate_is_reported_as_an_error() {
        expect_parse_error!(EmptyPredicate, tokens![
            name_test("*"),
            Const(LeftBracket),
            Const(RightBracket),
        ]);
    }

    #[test]
    fn relative_path_with_trailing_slash_is_reported_as_an_error() {
        expect_parse_error!(TrailingSlash, tokens![
            name_test("*"), Const(Slash)]);
    }

    #[test]
    fn filter_expression_with_trailing_slash_is_reported_as_an_error() {
        expect_parse_error!(TrailingSlash, tokens![
            VarRef("variable".into()),
            Const(Slash),
        ]);
    }

    #[test]
    fn running_out_of_input_is_reported_as_an_error() {
        expect_parse_error!(RanOutOfInput, tokens![FnName("func".into())]);
    }

    #[test]
    fn having_extra_tokens_is_reported_as_an_error() {
        expect_parse_error!(ExtraUnparsedTokens, tokens![Const(LeftBracket)]);
    }

    #[test]
    fn a_tokenizer_error_is_reported_as_an_error() {
        expect_parse_error!(Lexer(UnableToCreateToken), vec![
            Ok(FnName("func".into())),
            Err(UnableToCreateToken)
        ]);
    }
}
