//! Semantical partial evaluation analysis.

use crate::*;
use crate::memory_manager::MemoryManager;
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
    fn propagate_unop(
        &self,
        unop: UnOp,
        a: Expr,
        arg: Expr,
        mem: &mut MemoryManager,
    ) -> (Expr, Expr) {
        use UnOp::*;
        let arg = match unop {
            Neg => neg(arg).simplify(mem),
            Abs => abs(arg).simplify(mem),
            Recip => recip(arg).simplify(mem),
            Sqrt => sqrt(arg).simplify(mem),
            Step => step(arg).simplify(mem),
            Sin => sin(arg).simplify(mem),
            Exp => exp(arg).simplify(mem),
            Ln => ln(arg).simplify(mem),
            Id => arg,
        };
        (a, arg)
    }
    fn propagate_binop(
        &self,
        binop: BinOp,
        (a, b): (Expr, Expr),
        (arg_a, arg_b): (Expr, Expr),
        mem: &mut MemoryManager,
    ) -> (Expr, Expr, Expr) {
        use BinOp::*;
        let arg = match binop {
            Add => add(arg_a, arg_b).simplify(mem),
            Mul => mul(arg_a, arg_b).simplify(mem),
            Max => max(arg_a, arg_b).simplify(mem),
            Min => min(arg_a, arg_b).simplify(mem),
        };
        (a, b, arg)
    }
}
