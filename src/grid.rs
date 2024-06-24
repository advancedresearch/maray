//! Grid.

use crate::*;

/// Stores a grid size.
pub struct Grid2(pub [u64; 2]);

impl Grid2 {
    /// Gets one cell of the grid as `(positions, uvs)`.
    pub fn cell(&self, pos: [u64; 2], quad: [Point2; 4]) -> ([Point2; 4], [Point2; 4]) {
        let w = nat(self.0[0]);
        let h = nat(self.0[1]);
        let fx = div(nat(pos[0]), w.clone());
        let fy = div(nat(pos[1]), h.clone());
        let gx = div(nat(pos[0] + 1), w.clone());
        let gy = div(nat(pos[1] + 1), h.clone());
        let uv0 = [fx.clone(), fy.clone()];
        let uv1 = [gx.clone(), fy];
        let uv2 = [fx, gy.clone()];
        let uv3 = [gx, gy];
        ([
            quad_pos(quad.clone(), uv0.clone()),
            quad_pos(quad.clone(), uv1.clone()),
            quad_pos(quad.clone(), uv2.clone()),
            quad_pos(quad.clone(), uv3.clone())
        ], [
            uv0,
            uv1,
            uv2,
            uv3,
        ])
    }
}
