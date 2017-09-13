//============================================================================//
// Imports:
//============================================================================//

use super::expr;
use super::expr::*;
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
                Filter => unimplemented!(),
            },
            Neg(ref expr) => pars_if(pt, pprec, 7, |pt| {
                pt.push(Const(CToken::MinusSign));
                expr.walk(pt, 7)
            }),
            /*
            Var(ref qn) => unimplemented!(),
            Apply(ref qn, ref args) => unimplemented!(),
            Path(ref start, ref steps) => unimplemented!(),
            Literal(ref lit) => unimplemented!(),
            ContextNode => unimplemented!(),
            RootNode => unimplemented!(),
            */
            _ => unimplemented!()
        }
    }
}