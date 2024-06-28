#[cfg(feature = "render")]
fn main() {
    use maray::*;
    use maray::sd::*;
    
    let size: [u32; 2] = [512; 2];

    let fx = div(x(), nat(size[0] as u64));
    let fy = div(y(), nat(size[1] as u64));
    let p = [fx, fy];

    let center = [half(), half()];
    let tenth = div(nat(1), nat(10));
    let center2 = center.clone();

    let circle = Sd2::RoundedBox {
        b: [div(half(), nat(2)), half()],
        r: p4_same(tenth.clone()),
    }.inside().translate(center.clone());
    let circle2 = Sd2::Circle {
        r: recip(nat(3)),
    }.inside().translate(center2.clone());

    let shape = set_xor(circle, circle2).subst2(&p).simplify();
    let shape = compressor::compress(shape);

    let r = mul(shape.clone(), nat(255));
    let g = mul(shape.clone(), nat(255));
    let b = mul(shape.clone(), nat(255));

    let rt = Runtime::new();
    let method = RenderMethod::JIT {threads: 8, report: Report::None};
    gen(method, &rt, [r.clone(), g, b], "test.png", size);

    let r_str = format!("{}", shape);
    println!("{}\n{}", r_str, r_str.chars().count());
}

#[cfg(not(feature = "render"))]
fn main() {}
