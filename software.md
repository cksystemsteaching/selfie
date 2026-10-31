# Software

The tools Rotor and Bitme in this repository were co-developed at the Department of Computer Sciences of the University of Salzburg and at the Faculty of Information Technology of the Czech Technical University in Prague (CTU), where they were developed under the project Robotics and Advanced Industrial Production (Roboprox, reg. no. CZ.02.01.01/00/22_008/0004590), research objective RO 12.1.

## Rotor

- **Title of output:** Rotor – RISC-V-to-BTOR2/SMT-LIB model generator
- **Registration number / Internal identifier:** V3S registration pending, to be submitted under the title "Rotor – RISC-V-to-BTOR2/SMT-LIB model generator"
- **Version:** as in selfie main branch, file `tools/rotor.c`
- **Project title:** Robotics and Advanced Industrial Production
- **Project registration number:** CZ.02.01.01/00/22_008/0004590
- **Type of result:** software
- **Date of publication:** 26.11.2023 (initial commit)
- **Authors and contributors:** Christoph Kirsch, University of Salzburg, Department of Computer Sciences, and Czech Technical University in Prague, Faculty of Information Technology, ORCID 0000-0002-0961-0564; contact: christoph.kirsch@fit.cvut.cz
- **Keywords:** RISC-V; BTOR2; SMT-LIB; bounded model checking; binary code verification; code synthesis
- **URL of storage location:** https://github.com/cksystemsteaching/selfie/blob/main/tools/rotor.c

**Description (originality and distinctiveness):**

Rotor is a self-translating modeling engine that translates full RISC-V machine code, including the selfie system itself, into BTOR2 and SMT-LIB formulae. The formulae are satisfiable exactly when some input makes the code exit with a non-zero code, divide by zero, or access memory outside its segments. Rotor can also generate models for RISC-V code synthesis. Unlike source-level verifiers, it reasons directly about the binary that actually runs.

**Relevance to the project (RO 12.1 – Scalable Symbolic Execution through Bounded Model Checking):**

Rotor is the bounded code modelling prototype of RO 12.1 (Milestone 12.1.1). It replaces the Unicorn toolchain named in the RO with a design built from scratch that reduces model generation to linear time and space, pushing exponential explosion from the execution engine into the solver and thereby turning symbolic execution into bounded model checking. Its configurable models serve as benchmarks for state-of-the-art and project-specific solvers.

- **Link to technical documentation:** https://github.com/cksystemsteaching/selfie (README, section on rotor)
- **License:** BSD 2-Clause License
- **System requirements:** 64-bit system (LP64), C compiler (clang or gcc), make (optional); BTOR2/SMT-LIB solver (e.g. btormc, Boolector/Bitwuzla, Z3) to check generated models
- **Type of interface/API:** command-line interface (via selfie)
- **Links to related publications and/or datasets:** arXiv:2607.14137 (2026); related Rust implementation: https://github.com/cksystemsteaching/rotor-rust
- **Naming convention of files/software:** `tools/rotor.c` in the selfie repository; generated models use `.btor2` / `.smt2` extensions

## Bitme

- **Title of output:** Bitme – concurrent bounded model checker for Rotor models
- **Registration number / Internal identifier:** V3S registration pending, to be submitted under the title "Bitme – concurrent bounded model checker for Rotor models"
- **Version:** as in selfie main branch, file `tools/bitme.py`
- **Project title:** Robotics and Advanced Industrial Production
- **Project registration number:** CZ.02.01.01/00/22_008/0004590
- **Type of result:** software
- **Date of publication:** 22.08.2024 (initial commit)
- **Authors and contributors:** Christoph Kirsch, University of Salzburg, Department of Computer Sciences, and Czech Technical University in Prague, Faculty of Information Technology, ORCID 0000-0002-0961-0564; contact: christoph.kirsch@fit.cvut.cz
- **Keywords:** bounded model checking; BTOR2; SMT solvers; binary decision diagrams; RISC-V
- **URL of storage location:** https://github.com/cksystemsteaching/selfie/blob/main/tools/bitme.py

**Description (originality and distinctiveness):**

Bitme is a concurrent bounded model checker that reasons about Rotor-generated models of RISC-V machine code. It combines SMT solvers and binary decision diagrams (BDDs) and runs them concurrently, using whichever technique resolves a given model first.

**Relevance to the project (RO 12.1 – Scalable Symbolic Execution through Bounded Model Checking):**

Bitme is the solver side of the RO 12.1 toolchain: it checks Rotor-generated models of RISC-V code and lets us study the performance of SMT, SAT and BDD-based reasoning on them. It thereby realizes the RO 12.1 goal of combining execution engine and solver into a single entity for scalable symbolic execution, and provides the basis for the bounded code minimization work of Milestone 12.1.2.

- **Link to technical documentation:** https://github.com/cksystemsteaching/selfie (README, section on bitme)
- **License:** BSD 2-Clause License
- **System requirements:** Python 3, no further dependencies; models produced by Rotor
- **Type of interface/API:** command-line interface
- **Links to related publications and/or datasets:** arXiv:2607.14137 (2026)
- **Naming convention of files/software:** `tools/bitme.py` in the selfie repository; input models in BTOR2 (`.btor2`)
