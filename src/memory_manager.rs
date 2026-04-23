//! Memory manager.

use crate::Expr;
use crate::compressor::Compressor;

use std::sync::Arc;

/// Stores reused sub-expressions.
///
/// Performs garbage collection when reaching modulus `gb` number of expressions.
pub struct MemoryManager {
    /// Stores shared sub-expressions.
    pub data: fnv::FnvHashSet<Arc<Expr>>,
    /// Maps sub-expressions.
    ///
    /// Used in simplify and rewrite process to speed up performance.
    /// In compression, this is cleared to make rewrites sound.
    ///
    /// This is a temporary data structure that gets cleared with `clear_tmp`.
    pub map: fnv::FnvHashMap<Arc<Expr>, Arc<Expr>>,
    /// Stores counts.
    ///
    /// Used in compression process to speed up performance.
    pub count: fnv::FnvHashMap<Arc<Expr>, Compressor>,
    /// The recurrent modulus size to trigger garbage collection.
    pub gb: usize,
}

impl MemoryManager {
    /// Creates a new memory manager.
    pub fn new(gb: usize) -> MemoryManager {
        MemoryManager {
            data: fnv::FnvHashSet::default(),
            map: fnv::FnvHashMap::default(),
            count: fnv::FnvHashMap::default(),
            gb,
        }
    }

    /// Clear temporary data structures.
    pub fn clear_tmp(&mut self) {
        self.map.clear();
        self.count.clear();
    }

    /// Get map.
    pub fn get_map(&mut self, expr: Arc<Expr>) -> Option<Arc<Expr>> {
        let mut res: Option<Arc<Expr>> = None;
        while let Some(a) = self.map.get(res.as_ref().unwrap_or(&expr)) {
            res = Some(a.clone());
        }
        res
    }

    /// Sets map.
    ///
    /// This should never be called when `a` equals `b`.
    pub fn set_map(&mut self, a: Arc<Expr>, b: Arc<Expr>) {
        self.map.insert(a, b);
    }

    /// Get count.
    pub fn get_count<'a>(&'a mut self, expr: &Arc<Expr>) -> &'a Compressor {
        if self.count.get(expr).is_none() {
            let c = Compressor::from_expr(expr, self);
            self.count.insert(expr.clone(), c);
        }
        self.count.get(expr).unwrap()
    }

    /// Get shared sub-expression.
    pub fn get(&mut self, expr: Expr) -> Arc<Expr> {
        if let Some(a) = self.data.get(&expr) {
            a.clone()
        } else {
            let a = Arc::new(expr);
            self.data.insert(a.clone());

            // Perform garbage collection.
            if self.data.len() % self.gb == self.gb - 1 {
                self.data.retain(|e| Arc::strong_count(e) > 1);
            }

            a
        }
    }
}
