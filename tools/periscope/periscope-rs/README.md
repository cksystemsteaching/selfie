# peRISCope

Small tool written as a part of my work for bachelor thesis. It can be used to
visualize simpler version of the witness format produced `btormc`, and for
benchmaring of `btormc`.

## Requirements

In order for some commands to successfully run, you need to have following tools
available on your system:

- [Rust](https://www.rust-lang.org/learn/get-started) toolchain for building,
  running and installation of the `periscope` binary.
- [boolector](https://boolector.github.io/) which provide the `btormc` binary.
- [`wc`](https://linux.die.net/man/1/wc) command for counting number of
  characters in model files.
- [hyperfine](https://github.com/sharkdp/hyperfine) - command line benchmarking
  tool
- [timeout](https://www.gnu.org/software/coreutils/manual/html_node/timeout-invocation.html) - command
  for running commands with a time limit.

## Build

To build this project you need to have Rust toolchain installed on your
computer. Check the [official website](https://www.rust-lang.org/tools/install)
for installation instructions.

After that, building is as simple as running:

```
cargo build
```

## Install

You can also install the program on your machine:

```
cargo install --path .
```

This will make the `periscope` command available in your terminal.

```
periscope --help
```

## Running

You can install the `periscope` as shown in the previous section. You can also
build and run directly using `cargo`:

```
cargo run -- <arguments_for_periscope>
```

For better performance, you can use the `--release` flag:

```
cargo run --release -- <arguments_for_periscope>
```

## Configuration

peRISCope uses a configuration file in either JSON or YAML format. Consult the
reference configuration for more information: 

```yaml
# optional timeout. If present, the `btormc` command will run no longer than the
# number of seconds specified here.
timeout: 300

# optional additional flags for btormc. Default is "-kmax 200"
btormc-flags: "-kmax 200"

# list of filenames to filter. Only models that match one of the filenames
# specified in this list will be benchmarked.
files:
  - "model1.btor"
  - "model2.btor"

# list of run names and corresponding arguments for `rotor`. The `rotor` will
# be run with these (additional) arguments, and the results of the run will be
# saved in file with the name of the run as filename.
runs:
  32-codewordsize: "0 -codewordsize 32"
  64-codewordsize: "0 -codewordsize 64"
```
