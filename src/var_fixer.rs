//! Fixes variables ids in expression.

use crate::*;

use std::collections::HashMap;

/// Fixes variable ids in expression.
pub struct VarFixer {
    /// Stores the id uniquely per expression.
    pub ids: HashMap<Expr, u64>,
    /// Used to generate new variable ids.
    pub var_count: u64,
}

impl VarFixer {
    /// Creates a new variable fixer.
    pub fn new() -> VarFixer {
        VarFixer {
            ids: HashMap::new(),
            var_count: 0,
        }
    }

    /// Fixes expression.
    pub fn fix(&mut self, expr: Expr, ctx: &mut Vec<(u64, u64)>) -> Expr {
        use Expr::*;

        match expr {
            X | Y | Tau | E | Nat(_) => expr,
            Var(n) => {
                for (old, new) in &*ctx {
                    if n == *old {return Var(*new)}
                }
                Var(n)
            }
            Neg(a) => Neg(Box::new(self.fix(*a, ctx))),
            Abs(a) => Abs(Box::new(self.fix(*a, ctx))),
            Recip(a) => Recip(Box::new(self.fix(*a, ctx))),
            Sqrt(a) => Sqrt(Box::new(self.fix(*a, ctx))),
            Step(a) => Step(Box::new(self.fix(*a, ctx))),
            Sin(a) => Sin(Box::new(self.fix(*a, ctx))),
            Exp(a) => Exp(Box::new(self.fix(*a, ctx))),
            Ln(a) => Ln(Box::new(self.fix(*a, ctx))),
            Add(ab) => Add(Box::new((self.fix(ab.0, ctx), self.fix(ab.1, ctx)))),
            Mul(ab) => Mul(Box::new((self.fix(ab.0, ctx), self.fix(ab.1, ctx)))),
            Max(ab) => Max(Box::new((self.fix(ab.0, ctx), self.fix(ab.1, ctx)))),
            Min(ab) => Min(Box::new((self.fix(ab.0, ctx), self.fix(ab.1, ctx)))),
            Let(mut ab) => {
                let mut new_ctx = vec![];
                for var in &mut ab.0.vars {
                    let expr = self.fix(var.1.clone(), ctx);
                    if let Some(id) = self.ids.get(&expr) {
                        new_ctx.push((var.0, *id));
                        var.0 = *id;
                    } else {
                        let id = self.var_count;
                        self.var_count += 1;
                        self.ids.insert(expr.clone(), id);
                        new_ctx.push((var.0, id));
                        var.0 = id;
                    }
                    var.1 = expr;
                }
                Let(Box::new((ab.0, self.fix(ab.1, &mut new_ctx))))
            }
            Decor(ab) => Decor(Box::new((self.fix(ab.0, ctx), ab.1))),
            App(abc) => App(Box::new((abc.0, self.fix(abc.1, ctx), self.fix(abc.2, ctx)))),
        }
    }
}

/// Fixes RGB channels in color such that a single `Cache` can be used for all channels.
pub fn fix_color(color: Color) -> Color {
    let [red, green, blue] = color;
    let mut var_fixer = var_fixer::VarFixer::new();
    [
        var_fixer.fix(red, &mut vec![]),
        var_fixer.fix(green, &mut vec![]),
        var_fixer.fix(blue, &mut vec![]),
    ]
}
