//! Semantical constant analysis.

use crate::*;
use semantics::{BinOp, Semantics, UnOp};

/// Semantical constant analysis.
#[derive(Copy, Clone)]
pub struct Constant;

impl Semantics for Constant {
    type Arg = ();
    fn init(&self, a: Expr, _arg: ()) -> Expr {
        Expr::Decor(Box::new((a, vec![var("const").into()])))
    }
    fn has(&self, a: &Expr) -> Option<()> {
        if a.has_decor_str("const") {Some(())} else {None}
    }
    fn should_init(&self, a: &Expr) -> Option<()> {
        use Expr::*;

        match a {
            Tau | E | Nat(_) => Some(()),
            _ => None,
        }
    }
    fn propagate_unop(&self, _unop: UnOp, a: Expr, _arg: ()) -> (Expr, ()) {
        (a, ())
    }
    fn propagate_binop(
        &self,
        _binop: BinOp,
        (a, b): (Expr, Expr),
        _args: ((), ())
    ) -> (Expr, Expr, ()) {
        (a, b, ())
    }
}
