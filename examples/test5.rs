#[cfg(feature = "render")]
fn main() {
    use maray::*;
    use std::sync::Arc;

    let rt = Runtime {
        functions: vec![
            ext_test,
        ],
        ctx: Arc::new(0.0_f64),
    };
    let expr = app(0, x(), y());
    println!("{}", expr);

    let color = [
        expr.clone(),
        expr.clone(),
        expr.clone(),
    ];
    let method = RenderMethod::JIT {threads: 8, report: Report::None};
    gen(method, &rt, color, "test.png", [128; 2]);
}

pub fn ext_test(ctx: &f64, _id: u32, _x: f64, _y: f64) -> f64 {*ctx}

#[cfg(not(feature = "render"))]
fn main() {}
