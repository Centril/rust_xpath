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

/// The result of running the lexer on some input.
pub type ParseResult<T> = Result<T, Error>;

//============================================================================//
// Parser, Trait:
//============================================================================//

pub trait XPathParser<'input> {
    type Expr: Expr;

    fn parse(&self, &'input str) -> ParseResult<Self::Expr>;
}

//============================================================================//
// Parser API:
//============================================================================//

/// An `XPath` expression parser.
struct Parser<'sm, SM: SubMaker<'sm> + 'sm>(SM, PhantomData<&'sm SM>);

impl<'sm, SM> Parser<'sm, SM>
where
    SM: SubMaker<'sm>
{
    /// Constructs a new parser.
    pub fn new(sm: SM) -> Self {
        Parser(sm, PhantomData)
    }

    pub fn into_submaker(self) -> SM {
        self.0
    }
}

impl<'input: 'sm, 'sm, SM> XPathParser<'input> for Parser<'sm, SM>
where
    SM: SubMaker<'sm>
{
    type Expr = SM::Exp;

    fn parse(&self, input: &'input str) -> ParseResult<Self::Expr> {
        let tokens = Lexer::new(input);
        let deabbr = LexerDeabbreviator::new(tokens);
        self.parse_iter(deabbr)
    }
}

impl<'sm, SM> Parser<'sm, SM>
where
    SM: SubMaker<'sm>
{
    pub fn parse_iter<'a: 'sm, I>(&self, source: I) -> ParseResult<SM::Exp>
    where
        I: Iterator<Item = LexerResult<'a>>,
    {
        let mut source = source.peekable();

        let expr = parse_or_expression(&mut source, &self.0)?;

        if source.has_more_tokens() {
            return Err(ExtraUnparsedTokens);
        }

        expr.ok_or(EmptyXPath)
    }
}

pub fn parse<'a, I, SM>(source: I, sm: &SM) -> ParseResult<SM::Exp>
where
    I: Iterator<Item = LexerResult<'a>>,
    SM: SubMaker<'a>
{
        let mut source = source.peekable();

        let expr = parse_or_expression(&mut source, sm)?;

        if source.has_more_tokens() {
            return Err(ExtraUnparsedTokens);
        }

        expr.ok_or(EmptyXPath)
}


pub trait SubMaker<'a> {
    type Exp: Expr;

    fn new(&self, exp: Self::Exp) -> <Self::Exp as Expr>::ExprSub;

    fn new_exprs(&self, exp: Vec<Self::Exp>) -> <Self::Exp as Expr>::ExprList;

    fn new_steps(&self, steps: Vec<<Self::Exp as Expr>::Steps>) -> <Self::Exp as Expr>::StepsList;

    fn new_lit(&self, s: &'a str) -> <Self::Exp as Expr>::L;

    fn new_prefix(&self, s: &'a str) -> <Self::Exp as Expr>::P;

    fn new_local(&self, s: &'a str) -> <Self::Exp as Expr>::S;
}



use super::str_strategy as ss;

use std::marker::PhantomData;

struct BoxSubMaker<
    'a,
    P = ss::BoxStrategy,
    S = ss::BoxStrategy,
    L = ss::BoxStrategy>
where
    P: ss::StrStrategy<'a>,
    S: ss::StrStrategy<'a>,
    L: ss::StrStrategy<'a>,
{
    s_prefix: P,
    s_localp: S,
    s_literal: L,
    ph: PhantomData<&'a ()>
}

impl<'a, P, S, L> Default for BoxSubMaker<'a, P, S, L>
where
    P: ss::StrStrategy<'a> + Default,
    S: ss::StrStrategy<'a> + Default,
    L: ss::StrStrategy<'a> + Default,
{
    fn default() -> Self {
        BoxSubMaker {
            s_prefix: Default::default(),
            s_localp: Default::default(),
            s_literal: Default::default(),
            ph: Default::default(),
        }
    }
}

impl<'a, P, S, L> SubMaker<'a> for BoxSubMaker<'a, P, S, L>
where
    P: ss::StrStrategy<'a>,
    S: ss::StrStrategy<'a>,
    L: ss::StrStrategy<'a>,
{
    type Exp = ExprB<P::Output, S::Output, L::Output>;

    fn new(&self, exp: Self::Exp) -> <Self::Exp as Expr>::ExprSub {
        Box::new(exp)
    }

    fn new_exprs(&self, exp: Vec<Self::Exp>) -> <Self::Exp as Expr>::ExprList {
        exp.into_boxed_slice()
    }

    fn new_steps(&self, steps: Vec<<Self::Exp as Expr>::Steps>) -> <Self::Exp as Expr>::StepsList {
        steps.into_boxed_slice()
    }

    fn new_lit(&self, s: &'a str) -> <Self::Exp as Expr>::L {
        self.s_literal.inject_str(s)
    }

    fn new_prefix(&self, s: &'a str) -> <Self::Exp as Expr>::P {
        self.s_prefix.inject_str(s)
    }

    fn new_local(&self, s: &'a str) -> <Self::Exp as Expr>::S {
        self.s_localp.inject_str(s)
    }
}

type BSM<'a> = BoxSubMaker<'a>;


//============================================================================//
// Internal: Types:
//============================================================================//

type TokenSource<'a, I> = &'a mut Peekable<I>;

type PRO<E> = ParseResult<Option<E>>;

type BinaryExpressionBuilder<E: Expr> = fn(E::ExprSub, E::ExprSub) -> E;

struct BinaryRule<E: Expr> {
    token: CToken,
    builder: BinaryExpressionBuilder<E>,
}

//============================================================================//
// Internal: Binary operator constructors:
//============================================================================//

macro_rules! new_bin_op {
    ($fn: ident, $op: expr) => {
        fn $fn<E>(l: E::ExprSub, r: E::ExprSub) -> E
        where
            E: Expr
        {
            E::new_bin($op, l, r)
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
    ($name: ident ($source: ident $(, $par: ident : $tpar: ty)*) -> $tret: ty { $($args:tt)* }) => {
        fn $name<'a, I>($source: TokenSource<I> $(, $par : $tpar)*) -> $tret
        where I: Iterator<Item = LexerResult<'a>>,
        {
            $($args)*
        }
    }
}

macro_rules! parser2 {
    ($name: ident ($source: ident, $sm: ident $(, $par: ident : $tpar: ty)*) -> $tret: ty { $($args:tt)* }) => {
        fn $name<'a: 'sm, 'sm, I, SM>($source: TokenSource<I>, $sm: &SM $(, $par : $tpar)*) -> $tret
        where
            I: Iterator<Item = LexerResult<'a>>,
            SM: SubMaker<'sm>,
        {
            $($args)*
        }
    }
}

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

fn brule<E: Expr>(ct: CToken, b: BinaryExpressionBuilder<E>) -> BinaryRule<E> {
    BinaryRule {
        token: ct,
        builder: b,
    }
}

//============================================================================//
// Internal: Parsers:
//============================================================================//


fn fix_qname<'sm, SM>(sm: &SM, qn: &tokens::QName<&'sm str>) -> expr::QName<<SM::Exp as Expr>::P, <SM::Exp as Expr>::S>
where
    SM: SubMaker<'sm>
{
    expr::QName(qn.0, qn.1).map(|s| sm.new_prefix(s), |s| sm.new_local(s))
}

fn fix_name_test<'sm, SM>(sm: &SM, nt: &tokens::NameTest<&'sm str>) -> expr::NameTest<<SM::Exp as Expr>::P, <SM::Exp as Expr>::S>
where
    SM: SubMaker<'sm>
{
    expr::NameTest {
        prefix: nt.0,
        local: nt.1
    }.map(|s| sm.new_prefix(s), |s| sm.new_local(s))
}

fn delim_par<'a: 'sm, 'sm, I, SM, F, T>(i: TokenSource<I>, sm: &SM, interior: F) -> ParseResult<T>
where
    I: Iterator<Item = LexerResult<'a>>,
    SM: SubMaker<'sm>,
    F: FnOnce(TokenSource<I>, &SM) -> ParseResult<T>,
{
    i.consume(LeftParen)?;
    let ret = interior(i, sm)?;
    i.consume(RightParen)?;
    Ok(ret)
}

parser2!(lassoc_parse(i, sm,
    child_parse: fn(TokenSource<I>, &SM) -> PRO<SM::Exp>,
    rules: &[BinaryRule<SM::Exp>]) -> PRO<SM::Exp> {
    let mut left = if let Some(x) = child_parse(i, sm)? { x }
                else { return Ok(None) };

    #[allow(never_loop)]
    'outer: while i.has_more_tokens() {
        for rule in rules {
            if i.consume_if_eq(rule.token) {
                let right = if let Some(x) = child_parse(i, sm)? { x }
                            else { return Err(RightHandSideExpressionMissing) };


                let ll = sm.new(left);
                let rr = sm.new(right);

                left = (rule.builder)(ll, rr);
                continue 'outer;
            }
        }

        break 'outer;
    }

    Ok(Some(left))
});

parser2!(first_matching_rule(i, sm,
    rules: &[fn(TokenSource<I>, &SM) -> PRO<SM::Exp>]) -> PRO<SM::Exp> {
    for sub in rules.iter() {
        let expr = (*sub)(i, sm)?;
        if expr.is_some() {
            return Ok(expr);
        }
    }

    Ok(None)
});

parser2!(parse_expression(i, sm) -> PRO<SM::Exp> {
    parse_or_expression(i, sm)
});

parser2!(parse_or_expression(i, sm) -> PRO<SM::Exp> {
    lassoc_parse(i, sm, parse_and_expression, &[brule(Or, new_or)])
});

parser2!(parse_and_expression(i, sm) -> PRO<SM::Exp> {
    lassoc_parse(i, sm, parse_equality_expression, &[brule(And, new_and)])
});

parser2!(parse_equality_expression(i, sm) -> PRO<SM::Exp> {
    lassoc_parse(i, sm, parse_relational_expression, &[
        brule(Equal, new_eq),
        brule(NotEqual, new_neq),
    ])
});

parser2!(parse_relational_expression(i, sm) -> PRO<SM::Exp> {
    lassoc_parse(i, sm, parse_additive_expression, &[
        brule(LessThan, new_lt),
        brule(LessThanOrEqual, new_le),
        brule(GreaterThan, new_gt),
        brule(GreaterThanOrEqual, new_ge),
    ])
});

parser2!(parse_additive_expression(i, sm) -> PRO<SM::Exp> {
    lassoc_parse(i, sm, parse_multiplicative_expression, &[
        brule(PlusSign, new_add),
        brule(MinusSign, new_sub),
    ])
});

parser2!(parse_multiplicative_expression(i, sm) -> PRO<SM::Exp> {
    lassoc_parse(i, sm, parse_unary_expression, &[
        brule(Multiply, new_mul),
        brule(Divide, new_div),
        brule(Remainder, new_rem),
    ])
});

parser2!(parse_unary_expression(i, sm) -> PRO<SM::Exp> {
    let expr = parse_union_expression(i, sm)?;
    if expr.is_some() {
        return Ok(expr);
    }

    i.consume_if_eq(MinusSign).failible_map(|_|
        parse_unary_expression(i, sm)?.map_or_else(
            || Err(RightHandSideExpressionMissing),
            |e| Ok(Some(SM::Exp::new_neg(sm.new(e)))),
        )
    )
});

parser2!(parse_union_expression(i, sm) -> PRO<SM::Exp> {
    lassoc_parse(i, sm, parse_path_expression, &[brule(Pipe, new_union)])
});

parser2!(parse_path_expression(i, sm) -> PRO<SM::Exp> {
    let expr = parse_location_path(i, sm)?;
    if expr.is_some() {
        return Ok(expr);
    } // TODO: investigate if this is a pattern

    parse_filter_expression(i, sm)?.failible_map(|expr| {
        if consume_slash(i) {
            parse_relative_location_path_raw(i, sm, expr)?
                .map_or_else(|| Err(TrailingSlash), |e| Ok(Some(e)))
        } else {
            Ok(Some(expr))
        }
    })
});

parser2!(parse_filter_expression(i, sm) -> PRO<SM::Exp> {
    parse_primary_expression(i, sm)?.failible_map(|expr| {
        Ok(Some(parse_predicates(i, sm)?.into_iter().fold(
            expr,
            |expr, pred| SM::Exp::new_filter(sm.new(expr), sm.new(pred)),
        )))
    })
});

parser2!(parse_location_path(i, sm) -> PRO<SM::Exp> {
    first_matching_rule(i, sm, &[
        parse_relative_location_path,
        parse_absolute_location_path,
    ])
});

parser2!(parse_absolute_location_path(i, sm) -> PRO<SM::Exp> {
    consume_slash(i).failible_map(|_|
        parse_relative_location_path_raw(i, sm, SM::Exp::new_root_node())
            .map(|path| path.or_else(|| Some(SM::Exp::new_root_node()))))
});

parser2!(parse_relative_location_path(i, sm) -> PRO<SM::Exp> {
    parse_relative_location_path_raw(i, sm, SM::Exp::new_context_node())
});

parser2!(parse_relative_location_path_raw(i, sm, start_point: SM::Exp) -> PRO<SM::Exp> {
    parse_step(i, sm)?.failible_map(|step| {
        let mut steps = vec![step];
        while consume_slash(i) {
            if let Some(next) = parse_step(i, sm)? { steps.push(next) }
            else { return Err(TrailingSlash) }
        }

        Ok(Some(SM::Exp::new_path(sm.new(start_point),
            sm.new_steps(steps))))
    })
});

parser2!(parse_step(i, sm) -> ParseResult<Option<<SM::Exp as Expr>::Steps>> {
    let axis = parse_axis(i)?;

    let node_test = if let Some(test) = parse_node_test(i, sm)? { Some(test) }
                    else { default_node_test(i, sm, axis)? };

    node_test.failible_map(|nt| parse_predicates(i, sm).map(|predicates|
        Some(<SM::Exp as Expr>::Steps::new_steps(axis, nt,
            sm.new_exprs(predicates)))
    ))
});

parser2!(parse_predicates(i, sm) -> ParseResult<Vec<SM::Exp>> {
    let mut predicates = Vec::new();
    while let Some(predicate) = parse_predicate_expression(i, sm)? {
        predicates.push(predicate)
    }
    Ok(predicates)
});

parser2!(parse_predicate_expression(i, sm) -> PRO<SM::Exp> {
    i.consume_if_eq(LeftBracket).failible_map(|_| {
        parse_expression(i, sm)?.map_or_else(|| Err(EmptyPredicate), |predicate| {
            i.consume(RightBracket)?;
            Ok(Some(predicate))
        })
    })
});

parser2!(parse_primary_expression(i, sm) -> PRO<SM::Exp> {
    first_matching_rule(i, sm, &[
        parse_variable_reference,
        parse_nested_expression,
        parse_string_literal,
        parse_numeric_literal,
        parse_function_call,
    ])
});

parser2!(parse_nested_expression(i, sm) -> PRO<SM::Exp> {
    i.next_token_is(LeftParen)
     .failible_map(|()| delim_par(i, sm, parse_expression))
});

parser2!(parse_function_call(i, sm) -> PRO<SM::Exp> {
    consume_match!(i, Token::FnName).failible_map(|name|
        delim_par(i, sm, parse_function_args)
            .map(|args| sm.new_exprs(args))
            .map(|arguments| Some(SM::Exp::new_app(
                fix_qname(sm, &name), arguments))))
});

parser2!(parse_function_args(i, sm) -> ParseResult<Vec<SM::Exp>> {
    let mut arguments = Vec::new();

    if let Some(arg) = parse_expression(i, sm)? { arguments.push(arg) }
    else { return Ok(arguments) }

    while i.consume_if_eq(Comma) {
        if let Some(arg) = parse_expression(i, sm)? { arguments.push(arg) }
        else { return Err(ArgumentMissing) }
    }

    Ok(arguments)
});

parser2!(parse_numeric_literal(i, sm) -> PRO<SM::Exp> {
    Ok(consume_match!(i, Token::Number).map(|x| SM::Exp::new_lit(x.into())))
});

parser2!(parse_string_literal(i, sm) -> PRO<SM::Exp> {
    Ok(parse_str(i, sm).map(LiteralValue::String).map(SM::Exp::new_lit))
});

parser2!(parse_variable_reference(i, sm) -> PRO<SM::Exp> {
    Ok(consume_match!(i, Token::VarRef).map(|qn| fix_qname(sm, &qn))
        .map(SM::Exp::new_var))
});

parser2!(default_node_test(i, sm, axis: Axis) -> PRO<NodeTest< <SM::Exp as Expr>::P, <SM::Exp as Expr>::S >>
{
    Ok(consume_match!(i, Token::NTest)
        .map(|nt| fix_name_test(sm, &nt)).map(|name|
        match axis.principal_node_type() {
            PrincipalNodeType::Attribute => NodeTest::Attribute(name),
            PrincipalNodeType::Element => NodeTest::Element(name),
            PrincipalNodeType::Namespace => NodeTest::Namespace(name),
    }))
});

parser2!(parse_node_test(i, sm) -> PRO<NodeTest< <SM::Exp as Expr>::P, <SM::Exp as Expr>::S >>
{
    consume_match!(i, Token::NType).failible_map(|name| {
        delim_par(i, sm, |i, sm| Ok(Some(match name {
            NodeType::Text => NodeTest::Text,
            NodeType::Node => NodeTest::Node,
            NodeType::Comment => NodeTest::Comment,
            NodeType::ProcIns => NodeTest::ProcIns(parse_local(i, sm))
        })))
    })
});

parser2!(parse_str(i, sm) -> Option<<SM::Exp as Expr>::L> {
    consume_match!(i, Token::Literal).map(|s| sm.new_lit(s))
});

parser2!(parse_local(i, sm) -> Option<<SM::Exp as Expr>::S> {
    consume_match!(i, Token::Literal).map(|s| sm.new_local(s))
});

basic_parser!(parse_axis(i) -> ParseResult<Axis> {
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
        if self {
            cont(())
        } else {
            Ok(None)
        }
    }
}

use super::lexer::Lexer;
use super::lexer_deabbr::LexerDeabbreviator;

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

    fn parse_raw<'a, I>(input: I) -> ParseResult<ExprB>
    where
        I: IntoIterator<Item = LexerResult<'a>>
    {
        Parser::new(BSM::default()).parse_iter(input.into_iter())
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

    mod failing {
        use super::*;

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
}