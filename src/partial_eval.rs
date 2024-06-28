//! Semantical partial evaluation analysis.

use crate::*;
use semantics::*;

/// Semantical partial evaluation.
///
/// Preserves the value of nodes.
#[derive(Copy, Clone)]
pub struct PartialEval;

impl Semantics for PartialEval {
    type Arg = Expr;
    fn init(&self, a: Expr, arg: Expr) -> Expr {
        use token::Token::*;
        Expr::Decor(Box::new((a, vec![Token::Str("part_eval".into()), Space, arg.into()])))
    }
    fn has(&self, a: &Expr) -> Option<Expr> {
        use token::Token;
        if let Expr::Decor(ab) = a {
            if let Token::TokenExpr(expr) = &ab.1[2] {Some(expr.clone())}
            else {None}
        } else {None}
    }
    fn should_init(&self, a: &Expr) -> Option<Expr> {
        use Expr::*;

        match a {
            X | Y |
            Tau | E | Nat(_) | Var(_) => Some(a.clone()),
            _ => None,
        }
    }
    fn propagate_unop(&self, unop: UnOp, a: Expr, arg: Expr) -> (Expr, Expr) {
        use UnOp::*;
        let arg = match unop {
            Neg => neg(arg).simplify(),
            Abs => abs(arg).simplify(),
            Recip => recip(arg).simplify(),
            Sqrt => sqrt(arg).simplify(),
            Step => step(arg).simplify(),
            Sin => sin(arg).simplify(),
            Exp => exp(arg).simplify(),
            Ln => ln(arg).simplify(),
            Id => arg,
        };
        (a, arg)
    }
    fn propagate_binop(
        &self,
        binop: BinOp,
        (a, b): (Expr, Expr),
        (arg_a, arg_b): (Expr, Expr)
    ) -> (Expr, Expr, Expr) {
        use BinOp::*;
        let arg = match binop {
            Add => add(arg_a, arg_b).simplify(),
            Mul => mul(arg_a, arg_b).simplify(),
            Max => max(arg_a, arg_b).simplify(),
            Min => min(arg_a, arg_b).simplify(),
        };
        (a, b, arg)
    }
}
