//! Provides the abstract syntax tree (AST) for `XPath` expressions.

//============================================================================//
// Imports:
//============================================================================//

use super::str_strategy as ss;

//============================================================================//
// Expressions, Trait & Type:
//============================================================================//

/// Models an `XPath` expression, without explicitly determining the type.
/// This enables us to parse and evaluate expressions with different
/// implementation details without duplication.
///
/// This is the (untyped) "tagless final interpreter" version of expressions.
pub trait Expr : Sized {
    /// The type for sub-expressions.
    type ExprSub: AsRef<Self>;

    /// The type of a list of sub-expressions.
    type ExprList: AsRef<[Self]>;

    type Steps: Steps<Expr = Self>;

    /// The type of a list of steps.
    type StepsList: AsRef<[Self::Steps]>;

    /// The type of Prefix:es.
    type P: AsRef<str>;

    /// The type of LocalPart:s.
    type S: AsRef<str>;

    /// The type of string literals.
    type L: AsRef<str>;

    /// Converts from the given encoding to the initial one.
    /// No heap allocation may occur as a result of calling this.
    fn to_initial(&self) -> ExprU<Self>;

    /// Constructs a new expression from a binary operator and its two operands.
    fn new_bin(op: BinaryOp, left: Self::ExprSub, right: Self::ExprSub) -> Self;

    /// Constructs a new negation of a given expression.
    fn new_neg(l: Self::ExprSub) -> Self;

    /// Constructs a variable reference expression.
    fn new_var(var: QName<Self::P, Self::S>) -> Self;

    /// Constructs a new function application expression.
    fn new_app(fun: QName<Self::P, Self::S>, args: Self::ExprList) -> Self;

    /// Constructs a new path expression.
    fn new_path(start: Self::ExprSub, steps: Self::StepsList) -> Self;

    /// Constructs a new filtering expression.
    fn new_filter(subject: Self::ExprSub, predicate: Self::ExprSub) -> Self;

    /// Constructs a new literal expression.
    fn new_lit(lit: LiteralValue<Self::L>) -> Self;

    /// Constructs a new context node expression.
    fn new_context_node() -> Self;

    /// Constructs a new root node expression.
    fn new_root_node() -> Self;
}

/// Models an `XPath` expression using `Box` for sub-expressions.
#[derive(PartialEq, Clone, Debug)]
pub enum ExprB<P = B, S = B, L = B>
where
    P: AsRef<str>,
    S: AsRef<str>,
    L: AsRef<str>,
{
    /// A expression made up of a binary operator and its two boxed operands.
    Bin(BinaryOp, BExpr<P, S, L>, BExpr<P, S, L>),

    /// A negation of a boxed expression.
    Neg(BExpr<P, S, L>),

    /// A variable reference expression.
    Var(QName<P, S>),

    /// A function application expression.
    Apply(QName<P, S>, Box<[ExprB<P, S, L>]>),

    /// A path expression.
    Path(BExpr<P, S, L>, Box<[StepsB<P, S, L>]>),

    /// A filtering expression of a subject on LHS, and predicate on RHS.
    Filter(BExpr<P, S, L>, BExpr<P, S, L>),

    /// A literal value expression.
    Literal(LiteralValue<L>),

    /// A context node expression.
    ContextNode,

    /// A root node expression.
    RootNode,
}

/// Models an `XPath` expression using simple references for sub-expressions.
/// This allows creating expressions without any heap allocation at all.
#[derive(PartialEq, Clone, Debug)]
pub enum ExprR<'a, P = B, S = B, L = B>
where
    P: AsRef<str> + 'a,
    S: AsRef<str> + 'a,
    L: AsRef<str> + 'a,
{
    /// A expression made up of a binary operator and its two boxed operands.
    Bin(BinaryOp, ExprRR<'a, P, S, L>, ExprRR<'a, P, S, L>),

    /// A negation of an expression.
    Neg(ExprRR<'a, P, S, L>),

    /// A variable reference expression.
    Var(QName<P, S>),

    /// A function application expression.
    Apply(QName<P, S>, &'a [ExprR<'a, P, S, L>]),

    /// A path expression.
    Path(ExprRR<'a, P, S, L>, &'a [StepsB<P, S, L>]),
    
    /// A filtering expression of a subject on LHS, and predicate on RHS.
    Filter(ExprRR<'a, P, S, L>, ExprRR<'a, P, S, L>),

    /// A literal value expression.
    Literal(LiteralValue<L>),

    /// A context node expression.
    ContextNode,
    
    /// A root node expression.
    RootNode,
}

/// Models an `XPath` expression using simple references for sub-expressions.
/// This allows creating expressions without any heap allocation at all.
#[derive(PartialEq, Clone, Debug)]
pub enum ExprU<'a, Sub: Expr + 'a> {
    /// A expression made up of a binary operator and its two boxed operands.
    Bin(BinaryOp, &'a Sub, &'a Sub),

    /// A negation of an expression.
    Neg(&'a Sub),

    /// A variable reference expression.
    Var(QName<&'a str, &'a str>),

    /// A function application expression.
    Apply(QName<&'a str, &'a str>, &'a [Sub]),

    /// A path expression.
    Path(&'a Sub, &'a [StepsB<Sub::P, Sub::S, Sub::L>]),

    /// A filtering expression of a subject on LHS, and predicate on RHS.
    Filter(&'a Sub, &'a Sub),

    /// A literal value expression.
    Literal(LiteralValue<&'a str>),

    /// A context node expression.
    ContextNode,
    
    /// A root node expression.
    RootNode,
}

//============================================================================//
// Shorthands:
//============================================================================//

/// Shorthand for Box<str>.
type B = Box<str>;

/// Shorthand for `Box<Expr<...>>`.
pub(crate) type BExpr<P = B, S = B, L = B> = Box<ExprB<P, S, L>>;

/// Shorthand for `&'a ExprR<'a, ...>`.
pub(crate) type ExprRR<'a, P, S, L> = &'a ExprR<'a, P, S, L>;

//============================================================================//
// Implementations, Expressions:
//============================================================================//

impl<P, S, L> Expr for ExprB<P, S, L>
where
    P: AsRef<str>,
    S: AsRef<str>,
    L: AsRef<str>,
{
    type ExprSub = BExpr<P, S, L>;
    type ExprList = Box<[ExprB<P, S, L>]>;
    type Steps = StepsB<P, S, L>;
    type StepsList = Box<[StepsB<P, S, L>]>;
    type P = P;
    type S = S;
    type L = L;

    fn to_initial(&self) -> ExprU<Self> {
        use self::ExprB::*;
        match *self {
            Bin(op, ref l, ref r) => ExprU::Bin(op, l, r),
            Neg(ref expr) => ExprU::Neg(expr),
            Var(ref var) => ExprU::Var(var.borrowed()),
            Apply(ref f, ref a) => ExprU::Apply(f.borrowed(), a),
            Path(ref p, ref ss) => ExprU::Path(p, ss),
            Filter(ref s, ref p) => ExprU::Filter(s, p),
            Literal(ref lit) => ExprU::Literal(lit.borrowed()),
            ContextNode => ExprU::ContextNode,
            RootNode => ExprU::RootNode,
        }
    }

    fn new_bin(op: BinaryOp, left: Self::ExprSub, right: Self::ExprSub) -> Self {
        ExprB::Bin(op, left, right)
    }

    fn new_neg(expr: Self::ExprSub) -> Self {
        ExprB::Neg(expr)
    }

    fn new_var(var: QName<Self::P, Self::S>) -> Self {
        ExprB::Var(var)
    }

    fn new_app(fun: QName<Self::P, Self::S>, args: Self::ExprList) -> Self {
        ExprB::Apply(fun, args)
    }

    fn new_path(start: Self::ExprSub, steps: Self::StepsList) -> Self {
        ExprB::Path(start, steps)
    }

    fn new_filter(subject: Self::ExprSub, predicate: Self::ExprSub) -> Self {
        ExprB::Filter(subject, predicate)
    }

    fn new_lit(lit: LiteralValue<Self::L>) -> Self {
        ExprB::Literal(lit)
    }

    fn new_context_node() -> Self {
        ExprB::ContextNode
    }

    fn new_root_node() -> Self {
        ExprB::RootNode
    }
}

/*
impl<'a, P, S, L> ExprT for ExprR<'a, P, S, L>
where
    P: AsRef<str>,
    S: AsRef<str>,
    L: AsRef<str>,
{
    type ExprSub = &'a ExprR<'a, P, S, L>;
    type ExprList = &'a [ExprR<'a, P, S, L>];
    type StepsList = &'a [Steps<P, S, L>];
    type P = P;
    type S = S;
    type L = L;

    fn to_initial(&self) -> ExprU<Self> {
        use self::ExprR::*;
        match *self {
            Bin(op, l, r) => ExprU::Bin(op, l, r),
            Neg(expr) => ExprU::Neg(expr),
            Var(ref var) => ExprU::Var(var.borrowed()),
            Apply(ref f, a) => ExprU::Apply(f.borrowed(), a),
            Path(p, ref ss) => ExprU::Path(p, &ss),
            Filter(s, p) => ExprU::Filter(s, p),
            Literal(ref lit) => ExprU::Literal(lit.borrowed()),
            ContextNode => ExprU::ContextNode,
            RootNode => ExprU::RootNode,
        }
    }

    fn new_bin(op: BinaryOp, left: Self::ExprSub, right: Self::ExprSub) -> Self {
        ExprR::Bin(op, left, right)
    }

    fn new_neg(expr: Self::ExprSub) -> Self {
        ExprR::Neg(expr)
    }

    fn new_var(var: QName<Self::P, Self::S>) -> Self {
        ExprR::Var(var)
    }

    fn new_app(fun: QName<Self::P, Self::S>, args: Self::ExprList) -> Self {
        ExprR::Apply(fun, args)
    }

    fn new_path(start: Self::ExprSub, steps: Self::StepsList) -> Self {
        ExprR::Path(start, steps)
    }

    fn new_filter(subject: Self::ExprSub, predicate: Self::ExprSub) -> Self {
        ExprR::Filter(subject, predicate)
    }

    fn new_lit(lit: LiteralValue<Self::L>) -> Self {
        ExprR::Literal(lit)
    }

    fn new_context_node() -> Self {
        ExprR::ContextNode
    }

    fn new_root_node() -> Self {
        ExprR::RootNode
    }
}
*/

impl<'a, P, S, L> AsRef<ExprR<'a, P, S, L>> for ExprR<'a, P, S, L>
where
    P: AsRef<str>,
    S: AsRef<str>,
    L: AsRef<str>,
{
    fn as_ref(&self) -> &Self {
        self
    }
}

//============================================================================//
// Steps, Trait & Type:
//============================================================================//

pub trait Steps: Sized {
    type Expr: Expr;

    fn new_steps(
        axis: Axis,
        node_test: NodeTest<<Self::Expr as Expr>::P, <Self::Expr as Expr>::S>,
        predicates: <Self::Expr as Expr>::ExprList) -> Self;
}

#[derive(PartialEq, Clone, Debug)]
pub struct StepsB<P = B, S = B, L = B>
where
    P: AsRef<str>,
    S: AsRef<str>,
    L: AsRef<str>,
{
    pub axis: Axis,
    pub node_test: NodeTest<P, S>,
    pub predicates: Box<[ExprB<P, S, L>]>,
}

//============================================================================//
// Implementations, Steps:
//============================================================================//

impl<P, S, L> Steps for StepsB<P, S, L>
where
    P: AsRef<str>,
    S: AsRef<str>,
    L: AsRef<str>,
{
    type Expr = ExprB<P, S, L>;
    
    fn new_steps(
        axis: Axis,
        node_test: NodeTest<<Self::Expr as Expr>::P, <Self::Expr as Expr>::S>,
        predicates: <Self::Expr as Expr>::ExprList) -> Self
    {
        StepsB {
            axis, node_test, predicates
        }
    }
}

//============================================================================//
// Basic Types & Traits:
//============================================================================//

#[derive(PartialEq, Clone, Copy, Debug)]
pub enum PrincipalNodeType {
    Attribute,
    Element,
    Namespace,
}

#[derive(PartialEq, Clone, Copy, Debug)]
pub enum Axis {
    Ancestor,
    AncestorOrSelf,
    Attribute,
    Child,
    Descendant,
    DescendantOrSelf,
    Following,
    FollowingSibling,
    Namespace,
    Parent,
    Preceding,
    PrecedingSibling,
    SelfAxis,
}

/// A literal value that `XPath` supports.
#[derive(PartialEq, Clone, Copy, Debug)]
pub enum LiteralValue<L = B>
where
    L: AsRef<str>,
{
    /// A literal boolean.
    Boolean(bool),

    /// A literal number.
    Number(f64),

    /// A literal string.
    String(L),
}

//============================================================================//
// Functor API
//============================================================================//

impl<S: AsRef<str>> LiteralValue<S> {
    /// Applies a pure function mapping the string type of the NameTest.
    pub fn map<'a, F, T: 'a>(&'a self, f: F) -> LiteralValue<T>
    where
        T: AsRef<str>,
        F: Fn(&'a S) -> T,
    {
        use self::LiteralValue::*;
        match *self {
            Boolean(b) => Boolean(b),
            Number(n) => Number(n),
            String(ref s) => String(f(s))
        }
    }
}

impl<P: AsRef<str>, S: AsRef<str>> QName<P, S> {
    /// Applies pure functions mapping the string types of the QName.
    pub fn map<'a, F, T, G, U>(&'a self, f: F, g: G) -> QName<T, U>
    where
        T: AsRef<str>,
        U: AsRef<str>,
        F: Fn(&'a P) -> T,
        G: Fn(&'a S) -> U,
    {
        QName(self.0.as_ref().map(&f), g(&self.1))
    }
}

impl<P: AsRef<str>, S: AsRef<str>> NameTest<P, S> {
    /// Applies pure functions mapping the string types of the NameTest.
    pub fn map<'a, F, T, G, U>(&'a self, f: F, g: G) -> NameTest<T, U>
    where
        T: AsRef<str>,
        U: AsRef<str>,
        F: Fn(&'a P) -> T,
        G: Fn(&'a S) -> U,
    {
        NameTest {
            prefix: self.prefix.as_ref().map(&f),
            local: self.local.as_ref().map(&g),
        }
    }
}

//============================================================================//
// Functor API, AsRef<str> -> &str :
//============================================================================//

impl<S: AsRef<str>> LiteralValue<S> {
    /// Converts the string inside the literal value to a string slice.
    pub fn borrowed(&self) -> LiteralValue<&str> {
        self.map(|s| s.as_ref())
    }
}

impl<P: AsRef<str>, S: AsRef<str>> QName<P, S> {
    /// Converts the strings inside the qname value to string slices.
    pub fn borrowed(&self) -> QName<&str, &str> {
        self.map(|s| s.as_ref(), |s| s.as_ref())
    }
}





#[derive(PartialEq, Clone, Copy, Debug)]
pub struct NameTest<P = B, S = B>
where
    P: AsRef<str>,
    S: AsRef<str>,
{
    pub prefix: Option<P>,
    pub local: Option<S>,
}

#[derive(PartialEq, Clone, Copy, Debug)]
pub enum NodeTest<P = B, S = B>
where
    P: AsRef<str>,
    S: AsRef<str>,
{
    Node,
    Text,
    Comment,
    ProcIns(Option<S>),
    Attribute(NameTest<P, S>),
    Namespace(NameTest<P, S>),
    Element(NameTest<P, S>),
}

/// Denotes what binary operator an expression is.
#[derive(PartialEq, Clone, Copy, Debug)]
pub enum BinaryOp {
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
}

/// All the core functions `XPath` provides.
/// They are not represented as strings because they are required by the
/// standard to be provided, and thus it is more efficient to not potentially
/// box the function names when they are special.
///
/// See: https://www.w3.org/TR/xpath/#corelib for more details.
#[derive(PartialEq, Clone, Copy, Debug)]
pub enum CoreFunction {
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
}

/// Models a [`QName`].
///
/// [`QName`]: https://www.w3.org/TR/REC-xml-names/#ns-qualnames
#[derive(PartialEq, Clone, Debug)]
pub struct QName<P: AsRef<str> = B, S: AsRef<str> = B>(pub Option<P>, pub S);

//============================================================================//
// Implementations:
//============================================================================//

impl Axis {
    /// Describes what node type is naturally selected by this axis.
    pub fn principal_node_type(&self) -> PrincipalNodeType {
        match *self {
            Axis::Attribute => PrincipalNodeType::Attribute,
            Axis::Namespace => PrincipalNodeType::Namespace,
            _ => PrincipalNodeType::Element,
        }
    }
}

impl<L> From<f64> for LiteralValue<L>
where
    L: AsRef<str>,
{
    fn from(x: f64) -> Self {
        LiteralValue::Number(x)
    }
}


impl<P, S, L> From<LiteralValue<L>> for ExprB<P, S, L>
where
    P: AsRef<str>,
    S: AsRef<str>,
    L: AsRef<str>,
{
    fn from(x: LiteralValue<L>) -> Self {
        ExprB::Literal(x)
    }
}

impl<P, S, L> From<f64> for ExprB<P, S, L>
where
    P: AsRef<str>,
    S: AsRef<str>,
    L: AsRef<str>,
{
    fn from(x: f64) -> Self {
        ExprB::Literal(x.into())
    }
}

impl<P, S, L> From<QName<P, S>> for ExprB<P, S, L>
where
    P: AsRef<str>,
    S: AsRef<str>,
    L: AsRef<str>,
{
    fn from(x: QName<P, S>) -> Self {
        ExprB::Var(x)
    }
}

//============================================================================//
// Tests:
//============================================================================//



#[test]
fn expr_size_of() {
    use std::mem::size_of;

    println!("expr.rs!");

    println!("size_of BS:                  \t {:?}", size_of::<B>());

    println!("size_of Axis:                \t {:?}", size_of::<Axis>());

    println!(
        "size_of PrincipalNodeType:   \t {:?}",
        size_of::<PrincipalNodeType>()
    );

    println!(
        "size_of LiteralValue:        \t {:?}",
        size_of::<LiteralValue>()
    );

    println!(
        "size_of NameTest:            \t {:?}",
        size_of::<NameTest<&str>>()
    );

    println!(
        "size_of NodeTest:            \t {:?}",
        size_of::<NodeTest<&str>>()
    );

    println!(
        "size_of Steps:               \t {:?}",
        size_of::<StepsB<&str>>()
    );

    println!(
        "size_of Box<[Expr<P, S, L>]  \t {:?}",
        size_of::<Box<[ExprB<B, B, B>]>>()
    );

    println!(
        "size_of Box<Expr>:           \t {:?}",
        size_of::<BExpr<&str>>()
    );

    println!(
        "size_of Expr:                \t {:?}",
        size_of::<ExprB<&str>>()
    );
}

/*
#[test]
fn expr_boxed() {
    use str_strategy::StrStrategy;

    let ps = ss::HashSetStrategy::<&str>::default();
    let ss = ss::BoxStrategy::<&str>::default();
    let ls = ss::BoxStrategy::<&str>::default();
    let me = MasterExpr {
        expr: {
            let namet = NameTest {
                prefix: Some(ps.inject_str("company")),
                local: Some(ss.inject_str("data")),
            };
            let nt = NodeTest::Attribute(namet);
            let st = Steps {
                axis: Axis::Child,
                node_test: nt,
                predicates: vec![].into_boxed_slice(),
            };
            let rn = Box::new(Expr::RootNode);
            Expr::Path(rn, vec![st].into_boxed_slice())
        },
        s_prefix: ps,
        s_localp: ss,
        s_literal: ls,
    };

    use std;
    std::mem::drop(me)
}
*/
