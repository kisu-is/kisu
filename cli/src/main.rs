use std::path::PathBuf;

use argh::FromArgs;

#[derive(FromArgs)]
/// Kisu cli
struct Args {
    #[argh(positional)]
    path: Option<PathBuf>,

    #[argh(option, description = "kisu code", short = 'c')]
    code: Option<String>,
}

fn main() -> eyre::Result<()> {
    let args: Args = argh::from_env();

    if let Some(path) = args.path {
        let src = std::fs::read_to_string(path)?;
        let result = kisu::run(&src);
        println!("{result:?}");
    }

    if let Some(code) = args.code {
        let result = kisu::run(&code);
        println!("{result:?}");
    }

    Ok(())
}
