//============================================================================//
// Imports:
//============================================================================//

use unreachable::unreachable;
use itertools;
use itertools::Itertools;

use std::mem;
use std::iter::Peekable;

use super::expr;
use super::expr::*;
use super::tokens;
use super::tokens::*;
use super::tokens::CToken::*;
use super::lexer::{self, LexerResult};

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

impl<'str> From<StrToken<'str>> for Error {
    fn from(t: StrToken<'str>) -> Self {
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
///
/// This is a bit backwards... Expr should specify its allocator instead.
/// But since ATCs are not yet implemented, it is not possible.
/// This will be changed in a future version.
pub struct Parser<'alloc, A>
where
    A: Allocator<'alloc> + 'alloc
{
    allocator: A,
    dummy: PhantomData<&'alloc A>
}

impl<'alloc, A> Parser<'alloc, A>
where
    A: Allocator<'alloc>
{
    /// Constructs a new parser.
    pub fn new(alloc: A) -> Self {
        Parser {
            allocator: alloc,
            dummy: PhantomData
        }
    }

    /// Consumes the parser into the backing allocator.
    pub fn into_allocator(self) -> A {
        self.allocator
    }
}

impl<'input, 'alloc, A> XPathParser<'input> for Parser<'alloc, A>
where
    'input: 'alloc,
    A: Allocator<'alloc>,
{
    type Expr = A::Expr;

    fn parse(&self, input: &'input str) -> ParseResult<Self::Expr> {
        let tokens = Lexer::new(input);
        let deabbr = LexerDeabbreviator::new(tokens);
        println!("deabbr = {:?}", deabbr.clone().collect::<Vec<_>>());
        self.parse_iter(deabbr)
    }
}

impl<'alloc, A> Parser<'alloc, A>
where
    A: Allocator<'alloc>
{
    pub(crate) fn parse_iter<'input, I>(&self, source: I) -> ParseResult<A::Expr>
    where
        'input: 'alloc,
        I: Iterator<Item = LexerResult<'input>> + 'input + Clone,
    {
        let mut source = source.peekable();

        let expr = parse_or_expression(&mut source, &self.allocator)?;

        if source.has_more_tokens() {
            return Err(ExtraUnparsedTokens);
        }

        expr.ok_or(EmptyXPath)
    }
}

/*
pub fn parse<'a, I, SM>(source: I, sm: &SM) -> ParseResult<SM::Expr>
where
    I: Iterator<Item = LexerResult<'a>> + 'a,
    SM: Allocator<'a>
{
        let mut source = source.peekable();

        let expr = parse_or_expression(&mut source, sm)?;

        if source.has_more_tokens() {
            return Err(ExtraUnparsedTokens);
        }

        expr.ok_or(EmptyXPath)
}
*/

//============================================================================//
// Parser API: Expression allocators
//============================================================================//

/// Provides allocation mechanisms for the Parser.
/// The parser itself never directly allocates and instead the allocator
/// performs any needed allocation.
///
/// Through this mechanism, a variety of methods can be used for allocation,
/// including simply using `Box`, stack allocation, `typed_arena`.
pub trait Allocator<'input> {
    /// The type of expressions produced by this allocator.
    type Expr: Expr;

    /// Allocates a single expression.
    fn alloc(&self, exp: Self::Expr) -> <Self::Expr as Expr>::ExprSub;

    /// Allocates two expressions. Provided for optimization purposes.
    fn alloc_bin(&self, l: Self::Expr, r: Self::Expr)
        -> (<Self::Expr as Expr>::ExprSub, <Self::Expr as Expr>::ExprSub);

    /// Allocates a lazy iterator of possible expressions,
    /// in case any expression failed to parse and resulted in error,
    /// any allocation will be free'd and the entire computation results
    /// in an error.
    fn alloc_list<I>(&self, iter: I)
        -> ParseResult<<Self::Expr as Expr>::ExprList>
    where
        I: Iterator<Item = ParseResult<Self::Expr>>;

    /// Allocates a lazy iterator of possible steps,
    /// in case any expression failed to parse and resulted in error,
    /// any allocation will be free'd and the entire computation results
    /// in an error.
    fn alloc_steps<I>(&self, iter: I)
        -> ParseResult<<Self::Expr as Expr>::StepsList>
    where
        I: Iterator<Item = ParseResult<<Self::Expr as Expr>::Steps>>;

    /// Allocates a new string literal.
    fn alloc_lit(&self, s: &'input str) -> <Self::Expr as Expr>::L;

    /// Allocates a new prefix for a qname/node name.
    fn alloc_prefix(&self, s: &'input str) -> <Self::Expr as Expr>::P;

    /// Allocates a new local part for a qname/node name.
    fn alloc_local(&self, s: &'input str) -> <Self::Expr as Expr>::S;
}

use super::str_strategy as ss;

use std::marker::PhantomData;

struct BoxAllocator<
    'input,
    P = ss::BoxStrategy,
    S = ss::BoxStrategy,
    L = ss::BoxStrategy>
where
    P: ss::StrStrategy<'input>,
    S: ss::StrStrategy<'input>,
    L: ss::StrStrategy<'input>,
{
    s_prefix: P,
    s_localp: S,
    s_literal: L,
    ph: PhantomData<&'input ()>
}

impl<'input, P, S, L> Default for BoxAllocator<'input, P, S, L>
where
    P: ss::StrStrategy<'input> + Default,
    S: ss::StrStrategy<'input> + Default,
    L: ss::StrStrategy<'input> + Default,
{
    fn default() -> Self {
        BoxAllocator {
            s_prefix: Default::default(),
            s_localp: Default::default(),
            s_literal: Default::default(),
            ph: Default::default(),
        }
    }
}

impl<'input, P, S, L> Allocator<'input> for BoxAllocator<'input, P, S, L>
where
    P: ss::StrStrategy<'input>,
    S: ss::StrStrategy<'input>,
    L: ss::StrStrategy<'input>,
{
    type Expr = ExprB<P::Output, S::Output, L::Output>;

    fn alloc(&self, exp: Self::Expr) -> <Self::Expr as Expr>::ExprSub {
        Box::new(exp)
    }

    fn alloc_bin(&self, l: Self::Expr, r: Self::Expr) ->
        (<Self::Expr as Expr>::ExprSub, <Self::Expr as Expr>::ExprSub) {
        (self.alloc(l), self.alloc(r))
    }

    fn alloc_list<I>(&self, iter: I)
        -> ParseResult<<Self::Expr as Expr>::ExprList>
    where
        I: Iterator<Item = ParseResult<Self::Expr>>
    {
        failible_iter_to_boxslice(iter)
    }

    fn alloc_steps<I>(&self, iter: I)
        -> ParseResult<<Self::Expr as Expr>::StepsList>
    where
        I: Iterator<Item = ParseResult<<Self::Expr as Expr>::Steps>>
    {
        failible_iter_to_boxslice(iter)
    }

    fn alloc_lit(&self, s: &'input str) -> <Self::Expr as Expr>::L {
        self.s_literal.inject_str(s)
    }

    fn alloc_prefix(&self, s: &'input str) -> <Self::Expr as Expr>::P {
        self.s_prefix.inject_str(s)
    }

    fn alloc_local(&self, s: &'input str) -> <Self::Expr as Expr>::S {
        self.s_localp.inject_str(s)
    }
}

fn failible_iter_to_boxslice<T, E, I>(iter: I) -> Result<Box<[T]>, E>
where
    I: Iterator<Item = Result<T, E>>
{
    itertools::process_results(iter, move |iter| {
        iter.collect_vec().into_boxed_slice()
    })
}

type BSM<'input> = BoxAllocator<'input>;

//============================================================================//
// Internal: Types:
//============================================================================//

type TokenSource<'input, I> = &'input mut Peekable<I>;

type PRO<E> = ParseResult<Option<E>>;
type PRONT<P, S> = PRO<NodeTest<P, S>>;

type BinaryExpressionBuilder<E, ES> = fn((ES, ES)) -> E;

type Rule<I, A, Expr> = fn(TokenSource<I>, &A) -> PRO<Expr>;

struct BinaryRule<E: Expr> {
    token: CToken,
    builder: BinaryExpressionBuilder<E, E::ExprSub>,
}

//============================================================================//
// Internal: Binary operator constructors:
//============================================================================//

macro_rules! new_bin_op {
    ($fn: ident, $op: expr) => {
        fn $fn<E>(operands: (E::ExprSub, E::ExprSub)) -> E
        where
            E: Expr
        {
            let (l, r) = operands;
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
new_bin_op!(new_filter, BinaryOp::Filter);

//============================================================================//
// Internal: Conversions:
//============================================================================//

fn fix_qname<'alloc, A>(sm: &A, qn: &tokens::QName<&'alloc str>)
    -> expr::QName<<A::Expr as Expr>::P, <A::Expr as Expr>::S>
where
    A: Allocator<'alloc>
{
    expr::QName::new(qn.prefix, qn.local)
        .map(|s| sm.alloc_prefix(s), |s| sm.alloc_local(s))
}

fn fix_name_test<'alloc, A>(alloc: &A, nt: &tokens::NameTest<&'alloc str>)
    -> expr::NameTest<<A::Expr as Expr>::P, <A::Expr as Expr>::S>
where
    A: Allocator<'alloc>
{
    expr::NameTest {
        prefix: nt.prefix,
        local: nt.local
    }.map(|s| alloc.alloc_prefix(s), |s| alloc.alloc_local(s))
}

//============================================================================//
// Internal: Parsing utilities:
//============================================================================//

trait XCompat<'input> {
    fn has_more_tokens(&mut self) -> bool;
    fn next_token_is(&mut self, token: CToken) -> bool;
    fn consume(&mut self, token: CToken) -> ParseResult<()>;
    fn consume_if_eq(&mut self, token: CToken) -> bool;
}

impl<'input, I> XCompat<'input> for Peekable<I>
where
    I: Iterator<Item = LexerResult<'input>>,
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
        fn $name<'input, I>($source: TokenSource<I> $(, $par : $tpar)*) -> $tret
        where
            // TODO: Remove Clone,
            I: Iterator<Item = LexerResult<'input>> + 'input + Clone,
        {
            $($args)*
        }
    }
}

macro_rules! parser {
    ($name: ident ($source: ident, $alloc: ident $(, $par: ident : $tpar: ty)*) -> $tret: ty { $($args:tt)* }) => {
        fn $name<'input, 'alloc, I, A>($source: TokenSource<I>, $alloc: &A $(, $par : $tpar)*) -> $tret
        where
            'input: 'alloc,
            I: Iterator<Item = LexerResult<'input>> + 'input + Clone,
            A: Allocator<'alloc> + 'alloc,
        {
            $($args)*
        }
    }
}

macro_rules! expr_parser {
    ($name: ident ($source: ident, $alloc: ident $(, $par: ident : $tpar: ty)*) { $($args:tt)* }) => {
        fn $name<'input, 'alloc, I, A>($source: TokenSource<I>, $alloc: &A $(, $par : $tpar)*) -> PRO<A::Expr>
        where
            'input: 'alloc,
            I: Iterator<Item = LexerResult<'input>> + 'input + Clone,
            A: Allocator<'alloc> + 'alloc,
        {
            $($args)*
        }
    }
}

fn delim_par<'input, 'alloc, I, A, F, T>(i: TokenSource<I>, alloc: &A, interior: F)
    -> ParseResult<T>
where
    'input: 'alloc,
    I: Iterator<Item = LexerResult<'input>>,
    A: Allocator<'alloc>,
    F: FnOnce(TokenSource<I>, &A) -> ParseResult<T>,
{
    i.consume(LeftParen)?;
    let ret = interior(i, alloc)?;
    i.consume(RightParen)?;
    Ok(ret)
}

expr_parser!(lassoc_parse(i, alloc,
    child_parse: fn(TokenSource<I>, &A) -> PRO<A::Expr>,
    rules: &[BinaryRule<A::Expr>]) {

    let mut left = if let Some(x) = child_parse(i, alloc)? { x }
                else { return Ok(None) };

    #[cfg_attr(feature = "cargo-clippy", allow(never_loop))]
    'outer: while i.has_more_tokens() {
        for rule in rules {
            if i.consume_if_eq(rule.token) {
                let right = if let Some(x) = child_parse(i, alloc)? { x }
                            else { return Err(RightHandSideExpressionMissing) };

                left = (rule.builder)(alloc.alloc_bin(left, right));
                continue 'outer;
            }
        }

        break 'outer;
    }

    Ok(Some(left))
});

expr_parser!(first_matching_rule(i, alloc, rules: &[Rule<I, A, A::Expr>]) {
    for sub in rules.iter() {
        let expr = (*sub)(i, alloc)?;
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

fn brule<E: Expr>(ct: CToken, b: BinaryExpressionBuilder<E, E::ExprSub>)
    -> BinaryRule<E>
{
    BinaryRule {
        token: ct,
        builder: b,
    }
}

fn failible_map<F, T, U, E>(opt: Option<T>, cont: F) -> Result<Option<U>, E>
where
    F: FnOnce(T) -> Result<Option<U>, E>
{
    opt.map_or_else(|| Ok(None), cont)
}

fn apply_or_none<F, U, E>(cond: bool, cont: F) -> Result<Option<U>, E>
where
    F: FnOnce() -> Result<Option<U>, E>
{
    if cond { cont() } else { Ok(None) }    
}

fn invert_opt_res<T, E, F>(
    ro: Result<Option<T>, E>,
    fail: F)
    -> Option<Result<T, E>>
where
    F: FnOnce() -> Option<Result<T, E>>
{
    match ro {
        Ok(Some(x)) => Some(Ok(x)),
        Ok(None) => fail(),
        Err(e) => Some(Err(e)),
    }
}

//============================================================================//
// Internal: Parsers:
//============================================================================//

expr_parser!(parse_expression(i, alloc) {
    parse_or_expression(i, alloc)
});

expr_parser!(parse_or_expression(i, alloc) {
    lassoc_parse(i, alloc, parse_and_expression, &[brule(Or, new_or)])
});

expr_parser!(parse_and_expression(i, alloc) {
    lassoc_parse(i, alloc, parse_equality_expression, &[brule(And, new_and)])
});

expr_parser!(parse_equality_expression(i, alloc) {
    lassoc_parse(i, alloc, parse_relational_expression, &[
        brule(Equal, new_eq),
        brule(NotEqual, new_neq),
    ])
});

expr_parser!(parse_relational_expression(i, alloc) {
    lassoc_parse(i, alloc, parse_additive_expression, &[
        brule(LessThan, new_lt),
        brule(LessThanOrEqual, new_le),
        brule(GreaterThan, new_gt),
        brule(GreaterThanOrEqual, new_ge),
    ])
});

expr_parser!(parse_additive_expression(i, alloc) {
    lassoc_parse(i, alloc, parse_multiplicative_expression, &[
        brule(PlusSign, new_add),
        brule(MinusSign, new_sub),
    ])
});

expr_parser!(parse_multiplicative_expression(i, alloc) {
    lassoc_parse(i, alloc, parse_unary_expression, &[
        brule(Multiply, new_mul),
        brule(Divide, new_div),
        brule(Remainder, new_rem),
    ])
});

expr_parser!(parse_unary_expression(i, alloc) {
    let expr = parse_union_expression(i, alloc)?;
    if expr.is_some() {
        return Ok(expr);
    }

    apply_or_none(i.consume_if_eq(MinusSign), ||
        parse_unary_expression(i, alloc)?.map_or_else(
            || Err(RightHandSideExpressionMissing),
            |e| Ok(Some(A::Expr::new_neg(alloc.alloc(e)))),
        ))
});

expr_parser!(parse_union_expression(i, alloc) {
    lassoc_parse(i, alloc, parse_path_expression, &[brule(Pipe, new_union)])
});

expr_parser!(parse_path_expression(i, alloc) {
    let expr = parse_location_path(i, alloc)?;
    if expr.is_some() {
        return Ok(expr);
    } // TODO: investigate if this is a pattern

    failible_map(parse_filter_expression(i, alloc)?, |expr| {
        if consume_slash(i) {
            parse_relative_location_path_raw(i, alloc, expr)?
                .map_or_else(|| Err(TrailingSlash), |e| Ok(Some(e)))
        } else {
            Ok(Some(expr))
        }
    })
});

expr_parser!(parse_filter_expression(i, alloc) {
    failible_map(parse_primary_expression(i, alloc)?, |expr| {
        itertools::process_results(Predicates::new(i, alloc), move |iter|
            iter.fold(expr, |expr, pred|
                new_filter(alloc.alloc_bin(expr, pred)))
        ).map(Some)
    })
});

expr_parser!(parse_location_path(i, alloc) {
    first_matching_rule(i, alloc, &[
        parse_relative_location_path,
        parse_absolute_location_path,
    ])
});

expr_parser!(parse_absolute_location_path(i, alloc) {
    apply_or_none(consume_slash(i), ||
        parse_relative_location_path_raw(i, alloc, A::Expr::new_root_node())
            .map(|path| path.or_else(|| Some(A::Expr::new_root_node()))))
});

expr_parser!(parse_relative_location_path(i, alloc) {
    parse_relative_location_path_raw(i, alloc, A::Expr::new_context_node())
});

expr_parser!(parse_relative_location_path_raw(i, alloc, start_point: A::Expr) {
    failible_map(parse_step(i, alloc)?, |step| {
        let iter = itertools::unfold(Some(step), |init|
            if let Some(step) = init.take() {
                Some(Ok(step))
            } else if consume_slash(i) {
                invert_opt_res(parse_step(i, alloc),
                    || Some(Err(TrailingSlash)))
            } else { None }
        );

        alloc.alloc_steps(iter).map(|steps|
            Some(A::Expr::new_path(alloc.alloc(start_point), steps)))
    })
});

parser!(parse_step(i, alloc) -> ParseResult<Option<<A::Expr as Expr>::Steps>> {
    let axis = parse_axis(i)?;

    let node_test = if let Some(test) = parse_node_test(i, alloc)? { Some(test) }
                    else { default_node_test(i, alloc, axis)? };

    failible_map(node_test, |nt| parse_predicates(i, alloc).map(|predicates|
        Some(<A::Expr as Expr>::Steps::new_steps(axis, nt, predicates))
    ))
});

struct Predicates<'input, 'alloc, 'b, 'c, I, A>
where
    'input: 'alloc,
    I: Iterator<Item = LexerResult<'input>> + 'input + 'b,
    A: Allocator<'alloc> + 'c
{
    source: TokenSource<'b, I>,
    alloc: &'c A,
    dummy: PhantomData<&'alloc ()>
}

impl<'input, 'alloc, 'b, 'c, I, A> Predicates<'input, 'alloc, 'b, 'c, I, A>
where
    I: Iterator<Item = LexerResult<'input>>,
    A: Allocator<'alloc>,
{
    fn new(source: TokenSource<'b, I>, alloc: &'c A) -> Self {
        Predicates {
            source: source,
            alloc: alloc,
            dummy: PhantomData,
        }
    }
}

impl<'input, 'alloc, 'b, 'c, I, A> Iterator
for Predicates<'input, 'alloc, 'b, 'c, I, A>
where
    'input: 'alloc,
    I: Iterator<Item = LexerResult<'input>> + Clone,
    A: Allocator<'alloc> + 'alloc,
{
    type Item = ParseResult<A::Expr>;

    fn next(&mut self) -> Option<Self::Item> {
        invert_opt_res(parse_predicate_expression(self.source, self.alloc),
            || None)
    }
}

parser!(parse_predicates(i, alloc)
    -> ParseResult<<A::Expr as Expr>::ExprList>
{
    alloc.alloc_list(Predicates::new(i, alloc))
});

expr_parser!(parse_predicate_expression(i, alloc) {
    apply_or_none(i.consume_if_eq(LeftBracket), ||
        parse_expression(i, alloc)?.map_or_else(|| Err(EmptyPredicate),
            |predicate| {
                i.consume(RightBracket)?;
                Ok(Some(predicate))
            }
        )
    )
});

expr_parser!(parse_primary_expression(i, alloc) {
    first_matching_rule(i, alloc, &[
        parse_variable_reference,
        parse_nested_expression,
        parse_string_literal,
        parse_numeric_literal,
        parse_function_call,
    ])
});

expr_parser!(parse_nested_expression(i, alloc) {
    apply_or_none(i.next_token_is(LeftParen), ||
        delim_par(i, alloc, parse_expression))
});

expr_parser!(parse_function_call(i, alloc) {
    // TODO: fix change in lexer (no LeftParen)!
    failible_map(consume_match!(i, Token::FnName), |name|
        delim_par(i, alloc, parse_function_args)
            .map(|arguments| Some(A::Expr::new_app(
                fix_qname(alloc, &name), arguments))))
});

parser!(parse_function_args(i, alloc)
    -> ParseResult<<A::Expr as Expr>::ExprList>
{
    alloc.alloc_list(itertools::unfold(true, |mut first_arg| {
        if mem::replace(&mut first_arg, false) {
            invert_opt_res(parse_expression(i, alloc), || None)
        } else if i.consume_if_eq(Comma) {
            invert_opt_res(parse_expression(i, alloc),
                || Some(Err(ArgumentMissing)))
        } else { None }
    }))
});

expr_parser!(parse_numeric_literal(i, alloc) {
    #![allow(unused_variables)]
    Ok(consume_match!(i, Token::Number).map(|x| A::Expr::new_lit(x.into())))
});

expr_parser!(parse_string_literal(i, alloc) {
    Ok(parse_str(i, alloc).map(LiteralValue::String).map(A::Expr::new_lit))
});

expr_parser!(parse_variable_reference(i, alloc) {
    Ok(consume_match!(i, Token::VarRef).map(|qn| fix_qname(alloc, &qn))
        .map(A::Expr::new_var))
});

parser!(default_node_test(i, alloc, axis: Axis)
    -> PRONT< <A::Expr as Expr>::P, <A::Expr as Expr>::S >
{
    Ok(consume_match!(i, Token::NTest)
        .map(|nt| fix_name_test(alloc, &nt)).map(|name|
        match axis.principal_node_type() {
            PrincipalNodeType::Attribute => NodeTest::Attribute(name),
            PrincipalNodeType::Element => NodeTest::Element(name),
            PrincipalNodeType::Namespace => NodeTest::Namespace(name),
    }))
});

parser!(parse_node_test(i, alloc)
    -> PRONT<<A::Expr as Expr>::P, <A::Expr as Expr>::S>
{
    failible_map(consume_match!(i, Token::NType), |name| {
        match name {
            NodeType::Text => Ok(Some(NodeTest::Text)),
            NodeType::Node => Ok(Some(NodeTest::Node)),
            NodeType::Comment => Ok(Some(NodeTest::Comment)),
            NodeType::ProcIns => delim_par(i, alloc, |i, alloc|
                Ok(Some(NodeTest::ProcIns(parse_local(i, alloc)))))
        }
    })
});

parser!(parse_str(i, alloc) -> Option<<A::Expr as Expr>::L> {
    consume_match!(i, Token::Literal).map(|s| alloc.alloc_lit(s))
});

parser!(parse_local(i, alloc) -> Option<<A::Expr as Expr>::S> {
    consume_match!(i, Token::Literal).map(|s| alloc.alloc_local(s))
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

    fn parse_raw<'input, I>(input: I) -> ParseResult<ExprB>
    where
        I: IntoIterator<Item = LexerResult<'input>> + 'input,
        <I as IntoIterator>::IntoIter: Clone
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

    #[test]
    fn stuff() {
        let parser = Parser::new(BSM::default());
        println!("{:?}", parser.parse("1|2[3]").unwrap());

        println!();
        println!("{:?}", parser.parse("div[1]").unwrap());

        println!();
        println!("{:?}", parser.parse("1[2][3]").unwrap());
        println!("{:?}", parser.parse("(1[2])[3]").unwrap());
        println!("{:?}", parser.parse("1[(2[3])]").unwrap());

        println!();
        println!("{:?}", parser.parse(".").unwrap());
        println!("{:?}", parser.parse("self::node()").unwrap());

        println!();
        println!("{:?}", parser.parse("//.").unwrap());
        println!("{:?}", parser.parse("/descendant-or-self::node()/self::node()").unwrap());
        /*
        println!("{:?}", parser.parse("-1|2").unwrap());
        println!("{:?}", parser.parse("-(1 or 2)").unwrap());
        println!("{:?}", parser.parse("-1 or 2").unwrap());
        println!("{:?}", parser.parse("1 and 2 and 3").unwrap());
        println!("{:?}", parser.parse("1 and (2 and 3)").unwrap());
        println!("{:?}", parser.parse("(1 or 2) and 3").unwrap());
*/    }
}
