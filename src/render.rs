use crate::*;

/// Render to image using single thread.
pub fn single_gen_to_image<T, F>(
    r: Report,
    rt: &Runtime<T>,
    color: Color,
    img: &mut RgbImage,
    report: F
)
    where T: 'static + Clone,
          F: Fn(&mut RgbImage, f64)
{
    let color = var_fixer::fix_color(color);
    let (w, h) = img.dimensions();
    let ctx = Context::new();
    let ref mut cache = Cache::new();
    let ref mut rs = r.start();
    for y in 0..h {
        cache.clear();
        if r.update(rs, y) {report(img, y as f64 / h as f64)};
        for x in 0..w {
            let pixel = img.get_pixel_mut(x, y);
            cache.clear_dep_x();
            let p = [x as f64, y as f64];
            let r = color[0].eval2(rt, p, &ctx, cache) as u8;
            let g = color[1].eval2(rt, p, &ctx, cache) as u8;
            let b = color[2].eval2(rt, p, &ctx, cache) as u8;
            *pixel = Rgb([r, g, b]);
        }
    }
}

/// Render to image using Rayon and interpreter.
pub fn par_gen_to_image<T, F>(
    r: Report,
    rt: &Runtime<T>,
    color: Color,
    img: &mut RgbImage,
    report: F
)
    where T: 'static + Send + Sync + Clone,
          F: 'static + Fn(&mut RgbImage, f64) + Send,
{
    use rayon::iter::ParallelIterator;
    use rayon::iter::IntoParallelIterator;
    use std::sync::mpsc::channel;
    use std::sync::Mutex;
    use std::ops::DerefMut;

    let color = var_fixer::fix_color(color);
    let (w, h) = img.dimensions();
    let ctx = Context::new();
    let (sender, receiver) = channel::<(u32, Vec<Rgb::<u8>>)>();
    // Get the address of the image in a mutex,
    // knowing that the thread will be joined before returning.
    let img_mutex = Mutex::new(img as *mut RgbImage as usize);
    let join = std::thread::spawn(move || {
        let mut img_guard = img_mutex.lock().unwrap();
        let img = unsafe {&mut *(*img_guard.deref_mut() as *mut RgbImage)};
        let mut row_count = h;
        let ref mut rs = r.start();
        'outer: loop {
            let mut got_any: Option<u32> = None;
            std::thread::sleep(std::time::Duration::from_millis(10));
            while let Ok((y, row)) = receiver.try_recv() {
                if got_any.is_none() {
                    got_any = Some(y);
                } else {
                    got_any = got_any.map(|n| n.max(y));
                }
                for (x, pixel) in row.into_iter().enumerate() {
                    img.put_pixel(x as u32, y, pixel);
                }
                row_count -= 1;
                if row_count == 0 {break 'outer};
            }
            if let Some(y) = got_any {
                if r.update(rs, y) {report(img, y as f64 / h as f64)};
            };
        }
        drop(img_guard);
    });

    (0..h).into_par_iter().for_each(|y| {
        let ref mut cache = Cache::new();
        let mut res = vec![Rgb([0; 3]); w as usize];
        for (x, pixel) in res.iter_mut().enumerate() {
            cache.clear_dep_x();
            let p = [x as f64, y as f64];
            let r = color[0].eval2(rt, p, &ctx, cache) as u8;
            let g = color[1].eval2(rt, p, &ctx, cache) as u8;
            let b = color[2].eval2(rt, p, &ctx, cache) as u8;
            *pixel = Rgb([r, g, b]);
        }
        sender.send((y, res)).unwrap();
    });
    join.join().unwrap();
}

/// Render using WASM parallel generation.
pub fn wasm_par_gen_to_image<T, F>(
    r: Report,
    cpus: u32,
    rt: &Runtime<T>,
    color: Color,
    img: &mut RgbImage,
    report: F
)
    where T: 'static + Clone + Send + Sync,
          F: 'static + Fn(&mut RgbImage, f64) + Send,
{
    use std::sync::{Arc, Mutex};
    use std::sync::mpsc::channel;
    use std::ops::DerefMut;

    let color = var_fixer::fix_color(color);
    let (w, h) = img.dimensions();
    let (sender, receiver) = channel::<(u32, Vec<Rgb::<u8>>)>();
    // Get the address of the image in a mutex,
    // knowing that the thread will be joined before returning.
    let img_mutex = Mutex::new(img as *mut RgbImage as usize);
    let join = std::thread::spawn(move || {
        let mut img_guard = img_mutex.lock().unwrap();
        let img = unsafe {&mut *(*img_guard.deref_mut() as *mut RgbImage)};
        let mut row_count = h;
        let ref mut rs = r.start();
        'outer: loop {
            std::thread::sleep(std::time::Duration::from_millis(500));
            let mut got_any: Option<u32> = None;
            while let Ok((y, row)) = receiver.try_recv() {
                if got_any.is_none() {
                    got_any = Some(y);
                } else {
                    got_any = got_any.map(|n| n.max(y));
                }
                for (x, pixel) in row.into_iter().enumerate() {
                    img.put_pixel(x as u32, y, pixel);
                }
                row_count -= 1;
                if row_count == 0 {break 'outer};
            }
            if let Some(y) = got_any {
                if r.update(rs, y) {report(img, y as f64 / h as f64)};
            };
        }
        drop(img_guard);
    });

    let y_iter: Arc<Mutex<u32>> = Arc::new(0.into());
    let mut threads = vec![];
    for _ in 0..cpus {
        use wasm::Wasm;

        let sender = sender.clone();
        let y_iter = y_iter.clone();
        let color = color.clone();
        let rt = rt.clone();
        threads.push(std::thread::spawn(move || {
            let mut rt = rt;
            let rt_guard = current::CurrentGuard::new(&mut rt);

            let mut cr = Wasm::from_expr::<T>(&color[0]).unwrap();
            let mut cg = Wasm::from_expr::<T>(&color[1]).unwrap();
            let mut cb = Wasm::from_expr::<T>(&color[2]).unwrap();

            loop {
                let mut y_write = y_iter.lock().unwrap();
                let y = *y_write;
                if *y_write >= h {break}
                *y_write += 1;
                drop(y_write);

                let ref mut cache = Cache::new();
                let mut res = vec![Rgb([0; 3]); w as usize];
                for (x, pixel) in res.iter_mut().enumerate() {
                    cache.clear_dep_x();
                    let p = [x as f64, y as f64];
                    let r = cr.main.call(&mut cr.store, p[0], p[1]).unwrap() as u8;
                    let g = cg.main.call(&mut cg.store, p[0], p[1]).unwrap() as u8;
                    let b = cb.main.call(&mut cb.store, p[0], p[1]).unwrap() as u8;
                    *pixel = Rgb([r, g, b]);
                }
                sender.send((y, res)).unwrap();
            }

            drop(rt_guard);
        }))
    }
    drop(sender);

    for th in threads.into_iter() {th.join().unwrap()};
    join.join().unwrap();
}
