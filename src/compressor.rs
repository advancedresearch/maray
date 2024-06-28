//! Automatic compressor of math expression.

use crate::*;

/// Automatic compressor of math expression.
pub struct Compressor {
    /// The counted terms in expression.
    pub terms: Vec<(Expr, usize)>,
}

impl Compressor {
    /// Creates a new compressor.
    pub fn new() -> Compressor {
        Compressor {
            terms: vec![],
        }
    }

    /// Creates compressor from expression.
    pub fn from_expr(expr: &Expr) -> Compressor {
        let mut compressor = Compressor::new();
        compressor.count_expr(expr);
        compressor
    }

    /// Count expressions.
    pub fn count_expr(&mut self, expr: &Expr) {
        use Expr::*;

        match expr {
            X | Y | Tau | E | Nat(_) | Var(_) => return,
            _ => {}
        }

        let mut found = false;
        for term in &mut self.terms {
            if &term.0 == expr {
                term.1 += 1;
                found = true;
                break;
            }
        }
        if !found {self.terms.push((expr.clone(), 1))};

        match expr {
            X | Y | Tau | E | Var(_) | Nat(_) => {}
            Neg(a) | Abs(a) | Recip(a) | Sqrt(a) | Step(a) |
            Sin(a) | Exp(a) | Ln(a) => self.count_expr(a),
            Add(ab) | Mul(ab) | Max(ab) | Min(ab) => {
                self.count_expr(&ab.0);
                self.count_expr(&ab.1);
            }
            Let(_) => {}
            Decor(ab) => self.count_expr(&ab.0),
            App(abc) => {
                self.count_expr(&abc.1);
                self.count_expr(&abc.2);
            }
        }
    }

    /// Gets the last maximum benefit of compressing term.
    pub fn last_max_benefit(&self, min_count: usize, var_len: usize, cache: &mut IsCompressedCache) -> Option<(usize, usize)> {
        let mut res: Option<(usize, usize)> = None;
        for (i, term) in self.terms.iter().enumerate() {
            if term.1 < min_count {continue};
            if !cache.is_compressed(&term.0) {continue};
            let benefit = compression_benefit(&term.0, term.1, var_len);
            if benefit == 0 {continue};
            if let Some((_, max_benefit)) = res {
                if benefit >= max_benefit {
                    res = Some((i, benefit));
                }
            } else {
                res = Some((i, benefit));
            }
        }
        res
    }
}

/// Used to improve performance when determining whether expression is compressed.
pub struct IsCompressedCache(std::collections::HashMap<Expr, bool>);

impl IsCompressedCache {
    /// Creates a new cache.
    pub fn new() -> IsCompressedCache {
        IsCompressedCache(std::collections::HashMap::new())
    }

    /// Return true if expression is compressed.
    pub fn is_compressed(&mut self, expr: &Expr) -> bool {
        if let Some(v) = self.0.get(expr) {*v} else {
            let v = is_compressed(expr);
            self.0.insert(expr.clone(), v);
            v
        }
    }
}

/// Returns `true` if expression is compressed.
pub fn is_compressed(expr: &Expr) -> bool {
    let compressor = Compressor::from_expr(expr);
    for term in &compressor.terms {
        if term.1 > 1 {
            let benefit = compression_benefit(&term.0, term.1, 3);
            if benefit == 0 {continue}
            return false
        }
    }
    true
}

/// Calculates compression benefit of refactoring expression.
pub fn compression_benefit(expr: &Expr, count: usize, var_len: usize) -> usize {
    let expr_str = format!("{}", expr);
    // The first 3 is for ` = ` and
    // the second `3` is for line-shift and two spaces in front of variable.
    let len = expr_str.chars().count();
    let cost = var_len + 3 + len + 3;
    if var_len > len {return 0};
    let main = (len - var_len) * count;
    if cost > main {return 0};
    main - cost
}

/// Compresses the expression.
pub fn compress(expr: Expr) -> Expr {
    let mut res = expr;
    let mut ctx = Context::new();
    let ref mut cache = IsCompressedCache::new();
    let mut compressor = Compressor::new();
    let mut var_len = 2;
    loop {
        compressor.terms.clear();
        compressor.count_expr(&res);
        if let Some((ind, benefit)) = compressor.last_max_benefit(2, var_len, cache) {
            let id = ctx.vars.len() as u64;
            let formula = compressor.terms[ind].0.clone();
            eprintln!("Compressed {} terms, benefit {}\n  {}", ctx.vars.len() + 1, benefit, formula);
            let name = format!("a{}", id);
            var_len = name.chars().count();
            ctx.vars.push((id, formula));
            res = res.rewrite(&ctx);
        } else {break}
    }
    let_(ctx, res)
}
