//! Semantical partial reduction analysis.

use crate::*;
use semantics::*;

/// Semantical partial reduction.
///
/// Reduces nodes.
#[derive(Copy, Clone)]
pub struct PartialRed;

impl Semantics for PartialRed {
    type Arg = ();
    fn init(&self, a: Expr, _arg: ()) -> Expr {
        Expr::Decor(Box::new((a, vec![Token::Str("part_red".into())])))
    }
    fn has(&self, a: &Expr) -> Option<()> {
        if a.has_decor_str("part_red") {Some(())} else {None}
    }
    fn should_init(&self, a: &Expr) -> Option<()> {
        use Expr::*;

        match a {
            X | Y |
            Tau | E | Nat(_) | Var(_) => Some(()),
            _ => None,
        }
    }
    fn propagate_unop(&self, _unop: UnOp, a: Expr, _arg: ()) -> (Expr, ()) {
        (a.simplify(), ())
    }
    fn propagate_binop(
        &self,
        _binop: BinOp,
        (a, b): (Expr, Expr),
        _args: ((), ())
    ) -> (Expr, Expr, ()) {
        (a.simplify(), b.simplify(), ())
    }
}
