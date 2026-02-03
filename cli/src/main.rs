use indicatif::{ProgressBar, ProgressStyle};
use miette::Result;
use std::{path::PathBuf, time::Duration};

use argh::FromArgs;

#[derive(FromArgs)]
/// Kisu cli
struct Args {
    #[argh(positional)]
    path: Option<PathBuf>,

    #[argh(option, description = "kisu code", short = 'c')]
    code: Option<String>,
}

fn main() -> Result<()> {
    let args: Args = argh::from_env();

    if let Some(path) = args.path {
        let source = std::fs::read_to_string(path).map_err(|e| miette::miette!(e.to_string()))?;
        run(&source);
    }

    if let Some(source) = args.code {
        run(&source);
    }

    Ok(())
}

fn run(source: &str) {
    let pb = ProgressBar::new_spinner();
    pb.enable_steady_tick(Duration::from_millis(120));
    pb.set_style(
        ProgressStyle::with_template("{spinner:.blue} {msg:.magenta}")
            .unwrap()
            .tick_strings(&["⢎ ", "⠎⠁", "⠊⠑", "⠈⠱", " ⡱", "⢀⡰", "⢄⡠", "⢆⡀", ""]),
    );
    pb.set_message("Running kisu...");
    let result = kisu::run(source);
    pb.finish_with_message(format!("{result:?}"));
}
