use maray::*;

fn main() {
    let expr = p2_len([x(), y()]);
    let expr = compressor::compress(expr);
    let mut wasm = wasm::Wasm::from_expr::<()>(&expr).unwrap();

    let result = wasm.main.call(&mut wasm.store, 3.0, 4.0).unwrap();
    assert_eq!(result, 5.0);
}
