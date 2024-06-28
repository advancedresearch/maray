//! Variable cache.

use crate::*;

use std::collections::HashMap;

/// Used to improve performance of evaluation with variables.
pub struct Cache(pub HashMap<String, (f64, bool)>);

impl Cache {
    /// Creates a new cache.
    pub fn new() -> Cache {
        Cache(HashMap::new())
    }

    /// Clears cache.
    pub fn clear(&mut self) {self.0.clear()}

    /// Clears cached values that are dependent on X.
    pub fn clear_dep_x(&mut self) {
        self.0.retain(|_, (_, b)| !*b);
    }

    /// Return value and x-dependency.
    pub fn val<T>(&mut self, rt: &Runtime<T>, p: [f64; 2], name: &String, ctx: &Context) -> (f64, bool) {
        if let Some(v) = self.0.get(name) {*v}
        else {
            for var in &ctx.vars {
                if &var.0 == name {
                    let v = var.1.eval2(rt, p, ctx, self);
                    let dep_x = var.1.dep_x(rt, p, ctx, self);
                    self.0.insert(name.clone(), (v, dep_x));
                    return (v, dep_x);
                }
            }
            (std::f64::NAN, false)
        }
    }
}
