use maray::*;

fn main() {
    let size: [u32; 2] = [128; 2];
    let expr = nat(255) * x() / nat(size[0] as u64);
    let rt = Runtime::new();
    let color = [expr.clone(), expr.clone(), expr.clone()];
    let method = RenderMethod::SingleInterpreted {report: Report::Row(10)};
    gen(method, &rt, color, "test.png", size);
}