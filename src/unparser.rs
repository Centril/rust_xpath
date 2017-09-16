//============================================================================//
// Imports:
//============================================================================//

use itertools::Itertools;

use super::expr;
use super::expr::*;
use super::tokens;
use super::tokens::*;
use super::tokens::Token::*;

//============================================================================//
// Imports:
//============================================================================//

/*
trait TokenProducer<'a> {
    type Iter: Iterator<Item = Token<&'a str>>;

    fn into_iterator(&'a self) -> Self::Iter;
}

impl<'a, E: Expr> TokenProducer<'a> for E {
    type 
    fn into_iterator(&'a self) -> Self::Iter {
        match self.to_initial() {

        }
    }
}
*/

fn lpar_if<P: PushToken>(pt: &mut P, pprec: u8, sprec: u8) {
    if pprec > sprec {
        pt.push(Const(CToken::LeftParen));
    }
}

fn rpar_if<P: PushToken>(pt: &mut P, pprec: u8, sprec: u8) {
    if pprec > sprec {
        pt.push(Const(CToken::RightParen));
    }
}

fn pars_if<F, P: PushToken>(pt: &mut P, pprec: u8, sprec: u8, inner: F)
where
    F: FnOnce(&mut P)
{
    let cond = pprec > sprec;
    if cond {
        pt.push(Const(CToken::LeftParen));
    }

    inner(pt);

    if cond {
        pt.push(Const(CToken::RightParen));
    }
}

fn lassoc<P: PushToken>(
    pt: &mut P,
    lhs: &ExprB,
    rhs: &ExprB,
    pprec: u8,
    sprec: u8,
    tok: CToken,
) {
    pars_if(pt, pprec, sprec, |pt| {
        lhs.walk(pt, sprec);
        pt.push(Const(tok));
        rhs.walk(pt, sprec - 1);
    });
}

trait PushToken {
    fn push(&mut self, token: Token<&str>);
}

impl expr::Axis {
    fn walk<P: PushToken>(&self, pt: &mut P) {
        use expr::Axis::*;
        let axis = match *self {
            Child => AxisName::Child,
            SelfAxis => AxisName::SelfAxis,
            Parent => AxisName::Parent,
            Descendant => AxisName::Descendant,
            DescendantOrSelf => AxisName::DescendantOrSelf,
            Attribute => AxisName::Attribute,
            Namespace => AxisName::Namespace,
            Ancestor => AxisName::Ancestor,
            AncestorOrSelf => AxisName::AncestorOrSelf,
            PrecedingSibling => AxisName::PrecedingSibling,
            FollowingSibling => AxisName::FollowingSibling,
            Preceding => AxisName::Preceding,
            Following => AxisName::Following,
        };
        pt.push(Axis(axis));
    }
}

impl expr::LiteralValue {
    fn walk<P: PushToken>(&self, pt: &mut P) {
        pt.push(match *self {
            LiteralValue::Number(n) => Token::Number(n),
            LiteralValue::String(ref s) => Token::Literal(s),
        });
    }
}

impl expr::NameTest {
    fn walk<P: PushToken>(&self, pt: &mut P) {
        let nt = self.borrowed();
        let ntt = tokens::NameTest::new(nt.prefix, nt.local);
        pt.push(Token::NTest(ntt));
    }
}

impl expr::NodeTest {
    fn walk<P: PushToken>(&self, pt: &mut P) {
        use expr::NodeTest::*;
        match *self {
            Node => {
                pt.push(Token::NType(NodeType::Node));
                pt.push(Const(CToken::LeftParen));
                pt.push(Const(CToken::RightParen));
            },
            Text => {
                pt.push(Token::NType(NodeType::Text));
                pt.push(Const(CToken::LeftParen));
                pt.push(Const(CToken::RightParen));
            },
            Comment => {
                pt.push(Token::NType(NodeType::Comment));
                pt.push(Const(CToken::LeftParen));
                pt.push(Const(CToken::RightParen));
            },
            ProcIns(ref opi) => {
                pt.push(Token::NType(NodeType::ProcIns));
                pt.push(Const(CToken::LeftParen));
                if let Some(lit) = opi.as_ref() {
                    pt.push(Token::Literal(&lit));
                }
                pt.push(Const(CToken::RightParen));
            },
            Attribute(ref nt) => nt.walk(pt),
            Namespace(ref nt) => nt.walk(pt),
            Element(ref nt) => nt.walk(pt),
        }
    }
}

impl expr::StepsB {
    fn walk<P: PushToken>(&self, pt: &mut P) {
        // axis:
        self.axis.walk(pt);

        // nodetest:
        self.node_test.walk(pt);

        // predicates:
        self.predicates.iter().foreach(|pred| {
            pt.push(Const(CToken::LeftBracket));
            pred.walk(pt, 1);
            pt.push(Const(CToken::RightBracket));
        });
    }
}

impl ExprB {
    fn walk<P: PushToken>(&self, pt: &mut P, pprec: u8) {
        use self::ExprB::*;
        use self::BinaryOp::*;
        match *self {
            Bin(op, ref lhs, ref rhs) => match op {
                Or  => lassoc(pt, lhs, rhs, pprec, 1, CToken::Or),

                And => lassoc(pt, lhs, rhs, pprec, 2, CToken::And),

                Eq  => lassoc(pt, lhs, rhs, pprec, 3, CToken::Equal),
                NEq => lassoc(pt, lhs, rhs, pprec, 3, CToken::NotEqual),

                Lt  => lassoc(pt, lhs, rhs, pprec, 4, CToken::LessThan),
                LEq => lassoc(pt, lhs, rhs, pprec, 4, CToken::LessThanOrEqual),
                Gt  => lassoc(pt, lhs, rhs, pprec, 4, CToken::GreaterThan),
                GEq => lassoc(pt, lhs, rhs, pprec, 4, CToken::GreaterThanOrEqual),
                
                Add => lassoc(pt, lhs, rhs, pprec, 5, CToken::PlusSign),
                Sub => lassoc(pt, lhs, rhs, pprec, 5, CToken::MinusSign),

                Mul => lassoc(pt, lhs, rhs, pprec, 6, CToken::Multiply),
                Div => lassoc(pt, lhs, rhs, pprec, 6, CToken::Divide),
                Rem => lassoc(pt, lhs, rhs, pprec, 6, CToken::Remainder),

                Union => lassoc(pt, lhs, rhs, pprec, 8, CToken::Pipe),
                Filter => {
                    lhs.walk(pt, 9);
                    pt.push(Const(CToken::LeftBracket));
                    rhs.walk(pt, 1);
                    pt.push(Const(CToken::RightBracket));
                },
            },
            Neg(ref expr) => pars_if(pt, pprec, 7, |pt| {
                pt.push(Const(CToken::MinusSign));
                expr.walk(pt, 7)
            }),
            Var(ref qn) => {
                let qnb = qn.borrowed();
                let qnt = tokens::QName::new(qnb.prefix, qnb.local);
                pt.push(VarRef(qnt));
            },
            Apply(ref qn, ref args) => {
                let qnb = qn.borrowed();
                let qnt = tokens::QName::new(qnb.prefix, qnb.local);
                pt.push(FnName(qnt));
                for arg in args.iter() {
                    arg.walk(pt, 1);
                }
                pt.push(Const(CToken::RightParen));
            },
            Path(ref start, ref steps) => {
                start.walk(pt, 9);
                let mut iter = steps.iter();

                iter.next()
                    .expect("Malformed path, must have >= 1 step")
                    .walk(pt);

                while let Some(step) = iter.next() {
                    pt.push(Const(CToken::Slash));
                    step.walk(pt);
                }
            },
            Literal(ref lit) => lit.walk(pt),
            ContextNode => {},
            RootNode => pt.push(Const(CToken::Slash)),
        }
    }
}
