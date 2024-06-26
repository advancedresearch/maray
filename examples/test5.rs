use maray::*;
use std::sync::Arc;

fn main() {
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
    // gen(&rt, color, "test.png", [128; 2]);
    // par_gen(&rt, color, "test.png", [128; 2]);
    wasm_par_gen(8, &rt, color, "test.png", [128; 2]);
}

pub fn ext_test(ctx: &f64, _id: u32, _x: f64, _y: f64) -> f64 {*ctx}
