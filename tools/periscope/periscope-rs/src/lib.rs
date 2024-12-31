use std::path::PathBuf;

use clap::{Parser, Subcommand};

pub mod bench;
pub mod btor;

#[derive(Debug, Clone, Parser)]
#[clap(long_about)]
pub struct Config {
    /// Parse witness format of btormc generated from btor2 model. Parses from stdin if path to
    /// file is not provided.
    #[command(subcommand)]
    pub command: Commands,
}

#[derive(Debug, Clone, Subcommand)]
#[command(long_about)]
pub enum Commands {
    ParseWitness {
        /// Path to the witness file.
        file: Option<PathBuf>,

        /// Path to the BTOR2 model file, typically ends with '.btor2' extension.
        #[arg(short, long)]
        btor2: Option<PathBuf>,
    },

    Bench {
        /// Path to the results file where the benchmark results will be stored in JSON format.
        /// By default, the results will be stored in the '.periscope/bench/results.json' file.
        ///
        /// If 'run-rotor' flag is provided, then the results are stored in
        /// '.periscope/bench/results/{run-name}.json' regardless of this option.
        #[arg(long)]
        results_path: Option<PathBuf>,

        /// Whether to run rotor to generate files first.
        #[arg(short = 'r', long = "run-rotor")]
        run_rotor: bool,

        /// Files that should be benchmarked. Files that do not match the provided names will be
        /// ignored.
        ///
        /// The 'filter-files' option has priority if both 'filter-files' and 'filter-config' are
        /// provided.
        #[arg(short, long, requires = "run_rotor")]
        filter_files: Vec<String>,

        /// Config file that should be used for filtering. This is an alternative to using the
        /// 'filter-files' option. The file can be in JSON or YAML format.
        ///
        /// The 'filter-files' option has priority if both 'filter-files' and 'filter-config' are
        /// provided.
        ///
        /// # Example:
        ///
        /// ```yaml
        /// # timeout in seconds
        /// timeout: 300 # 5m = (5 * 60) s = 300 seconds
        /// files:
        ///   - "file1.btor2"
        ///   - "file2.btor2"
        ///   - "file3.btor3"
        ///
        /// runs:
        ///   8-bit-codeword-size: "0 -codewordsize 8"
        ///   16-bit-codeword-size: "0 -codewordsize 16"
        /// ```
        #[arg(short = 'c', long, requires = "run_rotor", verbatim_doc_comment)]
        bench_config: Option<PathBuf>,

        /// Path to the directory that contains selfie and rotor. You can clone selfie from
        /// [selfie's Github repository](https://www.github.com/cksystemsteaching/selfie).
        #[arg(short = 's', long = "selfie-dir", required_if_eq("run_rotor", "true"))]
        selfie_dir: Option<PathBuf>,

        /// Path to folder containing BTOR2 files. All BTOR2 files should have the ".btor2"
        /// extension. Alternatively, path to a single BTOR2 file can be provided for single
        /// benchmark.
        #[arg(required_unless_present("run_rotor"))]
        path: Option<PathBuf>,

        /// Target for runing `make` inside of the selfie directory.
        #[arg(short = 'm', long = "make-target", required_if_eq("run_rotor", "true"))]
        make_target: Option<String>,

        /// Number of parallel benchmarks to run. By default benchmarks are run sequentially.
        /// However, if you have multiple CPU cores, you can spin-up multiple benchmarks in
        /// parallel. Maximum value is 255.
        #[arg(short = 'j', long = "jobs", default_value = "1")]
        jobs: u8,
    },
}
