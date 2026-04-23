//! Semantical analysis.

use crate::Expr;
use crate::memory_manager::MemoryManager;

/// Unary operator.
#[derive(Copy, Clone)]
pub enum UnOp {
    /// Negative.
    Neg,
    /// Asboluste.
    Abs,
    /// Reciprocal (unary division).
    Recip,
    /// Square root.
    Sqrt,
    /// Step function.
    Step,
    /// Sine.
    Sin,
    /// Natural exponent.
    Exp,
    /// Natural logarithm.
    Ln,
    /// Identity is used in `Let` and `Decor`.
    Id,
}

/// Binary operator.
#[derive(Copy, Clone)]
pub enum BinOp {
    /// Addition.
    Add,
    /// Multiplication.
    Mul,
    /// Maximum.
    Max,
    /// Minimum.
    Min,
}

/// Used to simplify semantical analysis of expressions.
pub trait Semantics {
    /// The type of argument from value and semantics.
    type Arg;
    /// Initiate expression with semantics.
    fn init(&self, a: Expr, arg: Self::Arg) -> Expr;
    /// Whether expressions satisfies semantics decor.
    fn has(&self, a: &Expr) -> Option<Self::Arg>;
    /// Whether one should initiate expression with semantics.
    fn should_init(&self, a: &Expr) -> Option<Self::Arg>;
    /// Propagates unary operator.
    ///
    /// This should return the new inner expression with semantics.
    fn propagate_unop(
        &self,
        unop: UnOp,
        inner: Expr,
        arg: Self::Arg,
        mem: &mut MemoryManager
    ) -> (Expr, Self::Arg);
    /// Propagates binary operator.
    ///
    /// This should return the new inner expression with semantics.
    fn propagate_binop(
        &self,
        binop: BinOp,
        inner: (Expr, Expr),
        args: (Self::Arg, Self::Arg),
        mem: &mut MemoryManager,
    ) -> (Expr, Expr, Self::Arg);

    /// Decorate expression with semantics.
    fn decorate(&self, a: Expr) -> Expr {
        use Expr::*;

        if let Some(arg) = self.should_init(&a) {return self.init(a, arg)}
        match a {
            Neg(a) => Neg(Box::new(self.decorate(*a))),
            Abs(a) => Abs(Box::new(self.decorate(*a))),
            Recip(a) => Recip(Box::new(self.decorate(*a))),
            Sqrt(a) => Sqrt(Box::new(self.decorate(*a))),
            Step(a) => Step(Box::new(self.decorate(*a))),
            Sin(a) => Sin(Box::new(self.decorate(*a))),
            Exp(a) => Exp(Box::new(self.decorate(*a))),
            Ln(a) => Ln(Box::new(self.decorate(*a))),
            Add(ab) => {
                let a = self.decorate(ab.0);
                let b = self.decorate(ab.1);
                Add(Box::new((a, b)))
            }
            Mul(ab) => {
                let a = self.decorate(ab.0);
                let b = self.decorate(ab.1);
                Mul(Box::new((a, b)))
            }
            Max(ab) => {
                let a = self.decorate(ab.0);
                let b = self.decorate(ab.1);
                Max(Box::new((a, b)))
            }
            Min(ab) => {
                let a = self.decorate(ab.0);
                let b = self.decorate(ab.1);
                Min(Box::new((a, b)))
            }
            Let(ab) => {
                let a = ab.0;
                let b = self.decorate(ab.1);
                Let(Box::new((a, b)))
            }
            Decor(ab) => {
                let a = self.decorate(ab.0);
                let b = ab.1;
                Decor(Box::new((a, b)))
            }
            _ => a
        }
    }

    /// Propagates decor up the expression tree.
    fn propagate(&self, a: Expr, mem: &mut MemoryManager) -> Expr {
        use Expr::*;

        match a {
            Arc(inner) => {
                let a = self.propagate((*inner).clone(), mem);
                Arc(mem.get(a))
            }
            X | Y | Tau | E | Var(_) | Nat(_) => a,
            Exp(ref b) => {
                if let Some(arg) = self.has(b) {
                    let (new_inner, new_arg) =
                        self.propagate_unop(UnOp::Exp, decor_inner(b), arg, mem);
                    self.init(Exp(Box::new(new_inner)), new_arg)
                } else {
                    Exp(Box::new(self.propagate((**b).clone(), mem)))
                }
            }
            Ln(ref b) => {
                if let Some(arg) = self.has(b) {
                    let (new_inner, new_arg) =
                        self.propagate_unop(UnOp::Ln, decor_inner(b), arg, mem);
                    self.init(Ln(Box::new(new_inner)), new_arg)
                } else {
                    Ln(Box::new(self.propagate((**b).clone(), mem)))
                }
            }
            Sin(ref b) => {
                if let Some(arg) = self.has(b) {
                    let (new_inner, new_arg) =
                        self.propagate_unop(UnOp::Sin, decor_inner(b), arg, mem);
                    self.init(Sin(Box::new(new_inner)), new_arg)
                } else {
                    Sin(Box::new(self.propagate((**b).clone(), mem)))
                }
            }
            Neg(ref b) => {
                if let Some(arg) = self.has(b) {
                    let (new_inner, new_arg) =
                        self.propagate_unop(UnOp::Neg, decor_inner(b), arg, mem);
                    self.init(Neg(Box::new(new_inner)), new_arg)
                } else {
                    Neg(Box::new(self.propagate((**b).clone(), mem)))
                }
            }
            Abs(ref b) => {
                if let Some(arg) = self.has(b) {
                    let (new_inner, new_arg) =
                        self.propagate_unop(UnOp::Abs, decor_inner(b), arg, mem);
                    self.init(Abs(Box::new(new_inner)), new_arg)
                } else {
                    Abs(Box::new(self.propagate((**b).clone(), mem)))
                }
            }
            Recip(ref b) => {
                if let Some(arg) = self.has(b) {
                    let (new_inner, new_arg) =
                        self.propagate_unop(UnOp::Sin, decor_inner(b), arg, mem);
                    self.init(Recip(Box::new(new_inner)), new_arg)
                } else {
                    Recip(Box::new(self.propagate((**b).clone(), mem)))
                }
            }
            Sqrt(ref b) => {
                if let Some(arg) = self.has(b) {
                    let (new_inner, new_arg) =
                        self.propagate_unop(UnOp::Sin, decor_inner(b), arg, mem);
                    self.init(Sqrt(Box::new(new_inner)), new_arg)
                } else {
                    Sqrt(Box::new(self.propagate((**b).clone(), mem)))
                }
            }
            Step(ref b) => {
                if let Some(arg) = self.has(b) {
                    let (new_inner, new_arg) =
                        self.propagate_unop(UnOp::Sin, decor_inner(b), arg, mem);
                    self.init(Step(Box::new(new_inner)), new_arg)
                } else {
                    Step(Box::new(self.propagate((**b).clone(), mem)))
                }
            }
            Add(ref ab) => {
                if let (Some(arg_a), Some(arg_b)) = (self.has(&ab.0), self.has(&ab.1)) {
                    let (a, b, new_arg) =
                        self.propagate_binop(BinOp::Add,
                            (decor_inner(&ab.0), decor_inner(&ab.1)),
                            (arg_a, arg_b), mem);
                    self.init(Add(Box::new((a, b))), new_arg)
                } else {
                    let a = self.propagate(ab.0.clone(), mem);
                    let b = self.propagate(ab.1.clone(), mem);
                    Add(Box::new((a, b)))
                }
            }
            Mul(ref ab) => {
                if let (Some(arg_a), Some(arg_b)) = (self.has(&ab.0), self.has(&ab.1)) {
                    let (a, b, new_arg) =
                        self.propagate_binop(BinOp::Mul,
                            (decor_inner(&ab.0), decor_inner(&ab.1)),
                            (arg_a, arg_b), mem);
                    self.init(Mul(Box::new((a, b))), new_arg)
                } else {
                    let a = self.propagate(ab.0.clone(), mem);
                    let b = self.propagate(ab.1.clone(), mem);
                    Mul(Box::new((a, b)))
                }
            }
            Max(ref ab) => {
                if let (Some(arg_a), Some(arg_b)) = (self.has(&ab.0), self.has(&ab.1)) {
                    let (a, b, new_arg) =
                        self.propagate_binop(BinOp::Max,
                            (decor_inner(&ab.0), decor_inner(&ab.1)),
                            (arg_a, arg_b), mem);
                    self.init(Max(Box::new((a, b))), new_arg)
                } else {
                    let a = self.propagate(ab.0.clone(), mem);
                    let b = self.propagate(ab.1.clone(), mem);
                    Max(Box::new((a, b)))
                }
            }
            Min(ref ab) => {
                if let (Some(arg_a), Some(arg_b)) = (self.has(&ab.0), self.has(&ab.1)) {
                    let (a, b, new_arg) =
                        self.propagate_binop(BinOp::Min,
                            (decor_inner(&ab.0), decor_inner(&ab.1)),
                            (arg_a, arg_b), mem);
                    self.init(Min(Box::new((a, b))), new_arg)
                } else {
                    let a = self.propagate(ab.0.clone(), mem);
                    let b = self.propagate(ab.1.clone(), mem);
                    Min(Box::new((a, b)))
                }
            }
            Let(ref ab) => {
                if let Some(arg) = self.has(&ab.1) {
                    let (new_inner, new_arg) =
                        self.propagate_unop(UnOp::Id, decor_inner(&ab.1), arg, mem);
                    self.init(Let(Box::new((ab.0.clone(), new_inner))), new_arg)
                } else {
                    let a = ab.0.clone();
                    let b = self.propagate(ab.1.clone(), mem);
                    Let(Box::new((a, b)))
                }
            }
            Decor(_) => a,
            App(_) => a,
        }
    }
}

/// Gets the inner expression of decoration.
pub fn decor_inner(a: &Expr) -> Expr {
    if let Some(a) = a.decor_inner() {a.clone()} else {a.clone()}
}
