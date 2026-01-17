# Gemini Code Assistant Context

## Project Overview

This project, named "selfie," is an educational platform for teaching the design and implementation of programming languages and runtime systems. It is a self-contained C implementation of a compiler, an emulator, and a hypervisor.

The project consists of:

*   **starc:** A self-compiling compiler for a tiny subset of C called C* (`grammar.md`, `semantics.md`).
*   **mipster:** A self-executing emulator for a tiny subset of RISC-V called RISC-U (`riscu.md`).
*   **hypster:** A self-hosting hypervisor for RISC-U virtual machines.
*   **libcstar:** A tiny C* library.

The entire implementation is contained within a single C file, `selfie.c`.

## Building and Running

The project is built using `make`. The `Makefile` provides various targets for different tasks.

### Key Commands

*   **`make selfie`**: Compiles `selfie.c` into an executable named `selfie`. This is the primary build command.
*   **`./selfie -c <source.c> -o <output.m>`**: Compiles a C* source file (`<source.c>`) into a RISC-U binary (`<output.m>`).
*   **`./selfie -l <binary.m> -m <memory_in_mb>`**: Executes a RISC-U binary (`<binary.m>`) using the `mipster` emulator with the specified amount of memory.
*   **`make clean`**: Removes generated files.

The `Dockerfile` provides instructions for building a Docker image with all the necessary dependencies for running `selfie` and its related tools.

## Development Conventions

*   **Language:** The project is written in C*, a small subset of C. The grammar and semantics of C* are documented in `grammar.md` and `semantics.md`, respectively.
*   **Instruction Set:** The target instruction set is RISC-U, a minimal subset of RISC-V, documented in `riscu.md`.
*   **Code Style:** The code is well-documented with comments and follows a consistent style.
*   **Testing:** The `Makefile` includes several targets for running tests and checks, such as `self-self-check`.

## Tools

The `tools` directory contains a variety of tools that extend the functionality of `selfie`. These tools are built using the `Makefile` and can be used for tasks such as SAT solving, fuzzing, symbolic execution, and more.

Some of the key tools include:

*   **`babysat`**: A simple SAT solver.
*   **`beator`**: A bounded model checker for RISC-U code.
*   **`buzzr`**: A fuzzer for RISC-U code.
*   **`monster`**: A symbolic execution engine for RISC-U code.
*   **`rotor`**: A symbolic model generator for RISC-V code.

### Complex Tools

The `tools` directory also contains more complex tools in the following subdirectories:

*   **`bitme`**: A bounded model checker.
*   **`periscope`**: A tool for performance analysis.
*   **`quarc`**: A tool for quantum circuit synthesis.
*   **`qubot`**: A tool for quantum annealing.

## Key Files

*   `selfie.c`: The single source file containing the entire implementation of the compiler, emulator, and hypervisor.
*   `Makefile`: Contains all the build, run, and test commands.
*   `README.md`: Provides a comprehensive overview of the project, its goals, and how to use it.
*   `grammar.md`: Defines the grammar of the C* programming language.
*   `semantics.md`: Describes the semantic differences between C* and standard C.
*   `riscu.md`: Defines the RISC-U instruction set architecture.
*   `Dockerfile`: Defines the environment for building and running the project in a Docker container.
*   `examples/`: A directory containing various C* programs that can be compiled and run with `selfie`.
*   `tools/`: A directory containing various tools that extend the functionality of `selfie`.
