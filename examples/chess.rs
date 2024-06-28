use maray::*;
use maray::compressor::*;
use maray::grid::*;

fn main() {
    let size: [u32; 2] = [1024; 2];

    let fx = div(x(), nat(size[0] as u64));
    let fy = div(y(), nat(size[1] as u64));
    let p = [fx, fy];

    let texture = set_unit_square(chess(8));

    let grid = Grid2([8, 8]);

    let p1 = [recip(nat(5)), recip(nat(2))];
    let p2 = [sub(nat(1), recip(nat(5))), recip(nat(2))];
    let p3 = [nat(0), sub(nat(1), recip(nat(5)))];
    let p4 = [nat(1), sub(nat(1), recip(nat(5)))];

    let mut shape = nat(0);
    for i in 0..grid.0[0] {
        for j in 0..grid.0[1] {
            let (quad, uv) = grid.cell([i, j], [p1.clone(), p2.clone(), p3.clone(), p4.clone()]);

            let [(tri, uv), (tri2, uv2)] = quad_to_tri(quad, uv);

            let get_uv = texture.clone()
                .subst2(&to_uv(tri.clone(), uv, [x(), y()]));
            let shape1 = mul(inside_triangle(tri, [x(), y()]), get_uv)
                .subst2(&p);

            let get_uv2 = texture
                .subst2(&to_uv(tri2.clone(), uv2, [x(), y()]));
            let shape2 = mul(inside_triangle(tri2, [x(), y()]), get_uv2)
                .subst2(&p);

            shape = set_or(shape, set_or(shape1, shape2));
        }
    }

    let shape = shape.simplify();
    let shape = compress(shape);

    let r = mul(shape.clone(), nat(255));
    let g = mul(shape.clone(), nat(255));
    let b = mul(shape.clone(), nat(255));
    let color = [r, g, b];

    save("data/chess.maray", (size, color)).unwrap();

    let shape_str = format!("{}", shape);
    println!("\n{}\n\n{}", shape_str, shape_str.len());
}
