use super::str_strategy as ss;

pub enum PrincipalNodeType {
    Attribute,
    Element,
    Namespace,
}

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

type BS = Box<str>;

pub enum LiteralValue<L = BS>
where
    L: AsRef<str>,
{
    Boolean(bool),
    Number(f64),
    String(L),
}

pub struct NameTest<P = BS, S = BS>
where
    P: AsRef<str>,
    S: AsRef<str>,
{
    prefix: Option<P>,
    local: Option<S>,
}

pub enum NodeTest<P = BS, S = BS>
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

pub struct Steps<P = BS, S = BS, L = BS>
where
    P: AsRef<str>,
    S: AsRef<str>,
    L: AsRef<str>,
{
    axis: Axis,
    node_test: NodeTest<P, S>,
    predicates: Box<[Predicate<P, S, L>]>,
}

pub struct Predicate<P = BS, S = BS, L = BS>(Expr<P, S, L>)
where
    P: AsRef<str>,
    S: AsRef<str>,
    L: AsRef<str>;

type BExpr<P = BS, S = BS, L = BS> = Box<Expr<P, S, L>>;

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
    Mod,
    Union,
}

pub enum Expr<P = BS, S = BS, L = BS>
where
    P: AsRef<str>,
    S: AsRef<str>,
    L: AsRef<str>,
{
    Bin(BinaryOp, BExpr<P, S, L>, BExpr<P, S, L>),
    Neg(BExpr<P, S, L>),
    Var(BExpr<P, S, L>),
    Apply(S, Box<[Expr<P, S, L>]>),
    Path(BExpr<P, S, L>, Box<[Steps<P, S, L>]>),
    Filter(BExpr<P, S, L>, Box<Predicate<P, S, L>>),
    Literal(LiteralValue<L>),
    ContextNode,
    RootNode,
}

pub struct MasterExpr<
    'a,
    P = ss::HashSetStrategy<&'a str>,
    S = ss::BoxStrategy<&'a str>,
    L = ss::BoxStrategy<&'a str>,
> where
    P: ss::StrStrategy<'a>,
    S: ss::StrStrategy<'a>,
    L: ss::StrStrategy<'a>,
{
    s_prefix: P,
    s_localp: S,
    s_literal: L,
    expr: Expr<P::Output, S::Output, L::Output>,
}

#[test]
fn expr_size_of() {
    use std::mem::size_of;

    println!("expr.rs!");

    println!("size_of BS:                  \t {:?}", size_of::<BS>());

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
        size_of::<Steps<&str>>()
    );

    println!(
        "size_of Predicate:           \t {:?}",
        size_of::<Predicate<&str>>()
    );

    println!(
        "size_of Expr:                \t {:?}",
        size_of::<Expr<&str>>()
    );

    println!(
        "size_of MasterExpr:          \t {:?}",
        size_of::<MasterExpr>()
    );
}

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
