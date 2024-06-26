use maray::{open, wasm_par_gen, Runtime};
use clap::{Arg, ArgAction, Command};

fn main() -> anyhow::Result<()> {
    let matches = Command::new("Maray")
        .about("JIT Ray Tracing using basic math")
        .version("0.1")
        .arg(
            Arg::new("cpus")
                .short('c')
                .long("cpus")
                .action(ArgAction::Set)
                .num_args(1..2)
                .help("Number of CPU cores"),
        )
        .arg(
            Arg::new("input")
                .required(true)
                .short('i')
                .long("input")
                .action(ArgAction::Set)
                .num_args(1..2)
                .help("Input file `*.maray`"),
        )
        .arg(
            Arg::new("output")
                .required(true)
                .short('o')
                .long("output")
                .action(ArgAction::Set)
                .num_args(1..2)
                .help("Output file `*.png`"),
        )
        .get_matches();

    if let (Some(cpus), Some(file), Some(out_file)) =
        (matches.get_one::<String>("cpus"),
         matches.get_one::<String>("input"),
         matches.get_one::<String>("output"))
    {
        let cpus = u8::from_str_radix(cpus, 10)?;
        let (size, color) = open(&file)?;
        let rt = Runtime::new();
        wasm_par_gen(cpus as u8, &rt, color, &out_file, size);
    }
    Ok(())
}
