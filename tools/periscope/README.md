# peRISCope

This is a project for exploring the reasoning performance of RISC-V software
models in BTOR2. The name `periscope` is derived from the idea of exploring
PErformance of RISC models, and the idea of a periscope that can be used to
explore the unknown surroundings.

## Structure

The project consists of two sub-projects:

- [`periscope-rs`](./periscope-rs) - A binary written in Rust that can be used
  to parse witness format producec by `btormc`, and for benchmarking of model
  checking. Check the [README](./periscope-rs/README.md) for more information.
- [`periscope-py`](./periscope-py) - A Python package that can be used to read
  output of `periscope-rs` and produce plots. Check the
  [README](./periscope-py/README.md) for more information.
