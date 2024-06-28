#[cfg(feature = "render")]
fn main() -> anyhow::Result<()> {
    use maray::{open, gen, RenderMethod, Report, Runtime};
    use maray::textures::{self, Textures};
    use clap::{Arg, ArgAction, Command};
    use image::RgbImage;
    use std::time::Duration;

    let matches = Command::new("Maray")
        .about("JIT Ray Tracing using basic math")
        .version("0.1")
        .arg(
            Arg::new("cpus")
                .short('c')
                .long("cpus")
                .action(ArgAction::Set)
                .num_args(1..2)
                .help("Number of CPU cores")
        )
        .arg(
            Arg::new("input")
                .required(true)
                .short('i')
                .long("input")
                .action(ArgAction::Set)
                .num_args(1..2)
                .help("Input file `*.maray`")
        )
        .arg(
            Arg::new("output")
                .required(true)
                .short('o')
                .long("output")
                .action(ArgAction::Set)
                .num_args(1..2)
                .help("Output file `*.png`")
        )
        .arg(
            Arg::new("textures")
                .required(false)
                .short('t')
                .long("textures")
                .action(ArgAction::Set)
                .num_args(0..1024)
                .help("Texture file `*.png`")
        )
        .get_matches();

    if let (Some(cpus), Some(file), Some(out_file), textures) =
        (matches.get_one::<String>("cpus"),
         matches.get_one::<String>("input"),
         matches.get_one::<String>("output"),
         matches.get_many::<String>("textures"))
    {
        let cpus = u32::from_str_radix(cpus, 10)?;
        let (size, color) = open(&file)?;

        // Set up texture functions.
        let mut images = vec![];
        if let Some(textures) = textures {
            for file in textures {
                let image: RgbImage = image::open(file).unwrap().to_rgb8();
                images.push(image);
            };
        }
        let functions = textures::functions(images.len());

        let rt = Runtime::<Textures>::from_parts(
            textures::Textures {images}, functions
        );
        let method = RenderMethod::JIT {
            threads: cpus,
            report: Report::Duration(Duration::from_millis(500)),
        };
        gen(method, &rt, color, &out_file, size);
    }
    Ok(())
}

#[cfg(not(feature = "render"))]
fn main() {}
