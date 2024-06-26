//! A runtime context for a list of textures.

use image::RgbImage;

/// Stores a list of RGB images.
#[derive(Clone)]
pub struct Textures {
    /// The list of images.
    pub images: Vec<RgbImage>,
}

const ALIGN: u32 = 5;

/// Gets the function id for color channel.
pub fn channel(img: usize, ch: u8) -> u32 {(img as u32) * ALIGN + ch as u32}

/// Get the function id for image width.
pub fn image_width(img: usize) -> u32 {(img as u32) * ALIGN + 3}

/// Get the function id for image height.
pub fn image_height(img: usize) -> u32 {(img as u32) * ALIGN + 4}

/// Looks up color channel by `id = image * 3 + channel`.
pub fn fun_color_channel(ctx: &Textures, id: u32, x: f64, y: f64) -> f64 {
    let image = &ctx.images[(id / ALIGN) as usize];
    let (w, h) = image.dimensions();
    if x < 0.0 || y < 0.0 {return 0.0};

    let x = x as u32;
    let y = y as u32;
    if x >= w || y >= h {return 0.0};
    image.get_pixel(x, y)[(id % ALIGN) as usize] as f64
}

/// Looks up image width.
pub fn fun_image_width(ctx: &Textures, id: u32, _: f64, _: f64) -> f64 {
    let image = &ctx.images[(id / ALIGN) as usize];
    image.dimensions().0 as f64
}

/// Looks up image height.
pub fn fun_image_height(ctx: &Textures, id: u32, _: f64, _: f64) -> f64 {
    let image = &ctx.images[(id / ALIGN) as usize];
    image.dimensions().1 as f64
}

/// Generate list of functions for textures.
pub fn functions(n: usize) -> Vec<fn(&Textures, u32, f64, f64) -> f64> {
    let mut functions: Vec<fn(&Textures, u32, f64, f64) -> f64> =
        Vec::with_capacity(n * ALIGN as usize);
    for _ in 0..n {
        functions.push(fun_color_channel);
        functions.push(fun_color_channel);
        functions.push(fun_color_channel);
        functions.push(fun_image_width);
        functions.push(fun_image_height);
    };
    functions
}
