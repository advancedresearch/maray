//! Signed distance functions.

use crate::*;

/// Signed distance functions for 2D.
pub enum Sd2 {
    /// Circle.
    Circle {
        /// The radius of the circle.
        r: Expr
    },
    /// Box.
    Box {
        /// The half size of the box.
        b: Point2
    },
    /// Rounded box.
    RoundedBox {
        /// The half size of the box.
        b: Point2,
        /// The roundness of box corners.
        r: Point4
    },
}

impl Sd2 {
    /// Generates expression.
    pub fn to_expr(self) -> Expr {
        use Sd2::*;

        match self {
            Circle {r} => sub(p2_len([x(), y()]), r),
            Box {b} => {
                let d = p2_sub(p2_abs([x(), y()]), b);
                add(p2_len(p2_max(d.clone(), [nat(0), nat(0)])),
                    min(max(d[0].clone(), d[1].clone()), nat(0)))
            }
            RoundedBox {b, r} => {
                let rxy = p2_pos(x(), p4_xy(r.clone()), p4_zw(r.clone()));
                let rx = pos(y(), rxy[0].clone(), rxy[1].clone());
                let q = p2_add(p2_sub(p2_abs([x(), y()]), b), [rx.clone(), rx.clone()]);
                sub(add(
                    min(max(q[0].clone(), q[1].clone()), nat(0)),
                    p2_len(p2_max(q, [nat(0), nat(0)]))
                ), rx)
            }
        }
    }

    /// Get the set of points inside.
    pub fn inside(self) -> Expr {
        step(neg(self.to_expr()))
    }

    /// Get the set of points outside.
    pub fn outside(self) -> Expr {
        step(self.to_expr())
    }
}
