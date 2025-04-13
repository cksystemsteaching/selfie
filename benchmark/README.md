# BT - A Tool for Benchmarking and Analyzing SMT Models from C/C* Source Files

_This subproject of Selfie serves as a tool for analyzing and benchmarking SMT models generated from C/C* source files (and possibly more). The default model builder is Rotor (another Selfie subproject). BT is designed to be easily modifiable; it provides a framework for defining custom commands for generated models and for incorporating new model builders._

## Overview

SMT models generated from programming languages typically have very different characteristics from those created by traditional means (e.g. [SMT-COMP](https://smt-comp.github.io)). BT is built to serve as an analytical tool to find these differences, allowing you to compare typical SMT models with those generated from source code. BT also offers a simpler interface than Rotor for generating multiple models at once. This can mean generating from a single source file using different model types or by processing an entire directory of sources. It gives user the possibillity to generate different model types from a single source file and also generate models from entire directory. See section [bundles](#bundles) for more information.

## Model types
Model types are essentially different configurations for the model builders. These configurations can define:
- The register structure of the model (e.g., 32-bit or 64-bit),
- The model format language (such as SMT2 or BTOR2), and
- The machine word architecture (e.g., riscv, riscu, etc.).

These configurations are described in [config file](config.yml) and can be altered or added by a user.

For example, a model type like `starc-64bit-riscv-smt2` describes its source language, architecture, and model format. Models are described in a tree-like structure.

### Creating new model types
<a id="config-snippet"></a>
This is what the model type can look like in config file.
```yaml
models:
  starc:
    64bit:
      riscv: 
        btor2:
          command: "{rotor} -c {source_file} - 1 -o {output}"
        smt2: 
          command: "{rotor} -c {source_file}  - 1 -k -smt -nocomments -o {output}"
```
There are important rules that have to be followed for BT to be able to parse these model types.

1. Every path must end with a valid model format (also defined in config file), in the example it is `btor2` and `smt2`. Based on this key, BT will decide what parsers, presenters and model objects to create.
2. Every model format must also be followed by command key that tells BT how to invoke a model builder. (In current version BT assumes that every model builder will only need path to it's binary, a source file and optional output parameter.) 

---

## Features

- **Configuration:**  
  Easily configure model types and add new ones. You can also define alternative model builders besides Rotor.

- **Modularization:**  
  BT currently supports SMT2 and BTOR2 models (with support for C and C* source files, due to current limitations with Rotor). Its modular design enables developers to add additional model formats and support for new source languages and solvers.

- **Graphing:**  
  Generate graphs focused on analyzing the provided models, making it easier to visualize and interpret generated models (WIP - and later also benchmark results).

- **Bundle Generation:**  
  BT offers a flexible interface for generating models in bundles—easily process whole directories or generate variations from a single source with multiple commands.

## Requirements
- **Python Version:** Python 3.8+
- **Required tools:** `pip`
- **Dependencies:**: See [requirements.txt](requirements.txt)

## Installation

The simplest way to start is to run the `setup.sh` script. Script sets up a local virtual environment and installs all dependencies automatically.

```bash
./setup.sh && source venv/bin/activate
```
---
## Usage

BT is designed to be run from the command line. Below are some example invocations.
### Command-Line Options
Run the tool with `--help` for more details. For quick reference, here is the current help output:

```bash
$ python3 bt.py --help
Usage: bt.py [OPTIONS]

  A tool for benchmarking and analyzing SMT models.

Options:
  --source TEXT        Path to a source file or directory.
  --model-type TEXT    Specify the model configuration.
  --output PATH        Output directory for models and graphs.
  -g, --graph          Generate graphs.
  -v, --verbose        Increase verbosity.
  --help               Show this message and exit.
```
### Basic Command-Line Invocation

The general command syntax is:

```bash
python3 bt.py --source <source_file_or_directory> [--model-type <model_type>] [options]
```

For example, to generate two models (one in SMT2 format and one in BTOR2 format), generate graphs, and obtain verbose output—with all output placed in the `./models` directory—you can run:
```bash
python bt.py -s ../examples/symbolic/simple-if-else-1-35.c -m starc-64-bit-riscv -o ./models -g -v
```

### Displaying help
For a complete list of available options, run:
```bash
python bt.py -h
```

### Loading models
BT is also able to load models, this can be useful for analyzing models that are not generated (e.g. SMT-COMP benchmark models) or you want to analyze already generated models again.
```bash
python bt.py -l smt_comp_models/ -g
```
 An additional feature is that you can combine this with analyzing and benchmarking source files. The generated graphs will combine all loaded and newly generated models.
 ```bash
 python bt.py -l models/ -s ../examples/symbolic/ -m starc-64-bit-riscv-smt2 -g -v
 ```

### Using defined model types
As mentioned previously model types are defined in a tree-like structure inside a [config file](config.yml). To provide BT with a valid model type you can just follow it's structure in the config file. Each model type is a path from root to the leaf divided by '-'.


To generate a model using model type showcased [_Model types_](#config-snippet), BT can be called like this:
```bash
python bt.py --source {source} -m starc-64bit-riscv-smt2
```
Imporant to note is that although every model type needs to have a `command` key, user does not provide it as part of the argument when invoking BT.

---
## Bundles

### Source Files
The easiest way to process multiple source files is by specifying a whole directory. BT will parse the directory and pass all relevant sources to Rotor. (Note: In the current version, parsing is not recursive.)

**Example:**
```bash
python bt.py -s ../examples/symbolic
```

### Model Types
Within the provided [config file](config.yml), model types are structured hierarchically. Instead of specifying individual model types, you can indicate a branch. BT will then generate models for all leaf nodes of that branch, enabling mass model generation.

**Example:**
To generate models from configuration branch showcased in [_Model types_](#config-snippet), you might run:
```bash
python bt.py -m starc-64bit -s ../examples/symbolic/division-by-zero-3-35.c
```
---
## Solvers
Currently two SMT solvers are implemented in BT. [Bitwuzla](https://bitwuzla.github.io/) and [Z3](https://www.microsoft.com/en-us/research/project/z3-3/), both very powerful solvers tested in SMT-COMPs. They were chosen because they implement features that Rotor models use. Array and bit-vector theory and support for incremental solving. Solvers are currently invoked with default arguments. In future development this will be looked into.
## Graphs
TODO
