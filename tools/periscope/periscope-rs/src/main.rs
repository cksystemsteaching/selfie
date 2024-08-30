use std::{ffi::OsStr, io::Read, path::PathBuf};

use anyhow::Context;
use clap::Parser;
use periscope::{
    bench::{self, BenchConfig},
    btor::{self},
    Commands, Config,
};

fn main() -> anyhow::Result<()> {
    let config = Config::parse();

    match config.command {
        Commands::ParseWitness { file, btor2 } => {
            let witness: Box<dyn Read> = match file {
                Some(path) => Box::new(std::fs::File::open(path).unwrap()),
                None => Box::new(std::io::stdin()),
            };

            let btor2 = btor2.and_then(|path| {
                std::fs::File::open(path)
                    .inspect_err(|err| {
                        format!("Could not open provided btor2 file: {}", err);
                    })
                    .ok()
            });

            let witness = btor::parse_btor_witness(witness, btor2)?;

            witness.analyze_and_report();
        }
        Commands::Bench {
            path,
            run_rotor,
            results_path,
            filter_files,
            bench_config,
            selfie_dir,
            make_target,
            jobs,
        } => {
            let path = if run_rotor {
                selfie_dir.context("Selfie directory is required when running rotor.")?
            } else {
                path.context(
                    "Path to a BTOR2 file or directory containing BTOR2 files is required.",
                )?
            };

            let config = prepare_bench_config(run_rotor, filter_files, bench_config, results_path)?;

            bench::run_benches(path, config, make_target, jobs)?;
        }
    };

    Ok(())
}

/// Reads and deserializes the configuration file for benchmarking. If no file is provided, default
/// configuration values are used.
fn prepare_bench_config(
    run_rotor: bool,
    filter_files: Vec<String>,
    bench_config_path: Option<PathBuf>,
    results_path: Option<PathBuf>,
) -> anyhow::Result<BenchConfig> {
    let mut config = BenchConfig::default();

    if run_rotor {
        config = bench_config_path
            .map(|path| {
                let file = std::fs::File::open(&path)
                    .map_err(|err| anyhow::format_err!("Could not open config file: {err}"))?;

                match path.extension().and_then(OsStr::to_str) {
                    Some("json") => {
                        serde_json::from_reader(file).context("Config has invalid JSON format.")
                    }
                    Some("yaml") => {
                        serde_yaml::from_reader(file).context("Config has invalid YAML format.")
                    }
                    _ => anyhow::bail!("Config file must be in JSON or YAML format."),
                }
            })
            .transpose()?
            .unwrap_or_default();

        if !filter_files.is_empty() {
            config.files = filter_files;
        }
    }

    config.results_path = results_path;

    Ok(config)
}
