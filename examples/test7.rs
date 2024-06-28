#[cfg(feature = "render")]
fn main() {
    use maray::*;

    let size: [u32; 2] = [128; 2];
    let expr = nat(255) * x() / nat(size[0] as u64);
    let rt = Runtime::new();
    let color = [expr.clone(), expr.clone(), expr.clone()];
    let method = RenderMethod::JIT {threads: 1, report: Report::Row(10)};
    gen(method, &rt, color, "test.png", size);
}

#[cfg(not(feature = "render"))]
fn main() {}
