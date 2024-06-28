use maray::*;
use image::RgbImage;

fn main() {
    let size: [u32; 2] = [128; 2];
    let expr = nat(255) * x() / nat(size[0] as u64);
    let mut img = RgbImage::new(size[0], size[1]);
    let rt = Runtime::new();
    let color = [expr.clone(), expr.clone(), expr.clone()];
    wasm_par_gen_to_image(8, &rt, color, &mut img, |_, _| {});
    img.save("test.png").unwrap();
}
