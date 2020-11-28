# Selfie Bare-Metal Support

Selfie features bare-metal support in the form of a library operating system and a multitasking kernel. Both of them include the same rudiumentary filesystem that is constructed during compile-time and are able to execute programs written in C\*. They are built upon an implementation of [RISC-V's Supervisor Binary Interface](https://github.com/riscv/riscv-sbi-doc/) in the form of [OpenSBI](https://github.com/riscv/opensbi/) v0.7. Supported platforms are [QEMU](https://www.qemu.org/) v5.0, the [SiFive HiFive Unleashed](https://www.sifive.com/boards/hifive-unleashed), and the [Kendryte K210](https://canaan.io/product/kendryteai).

## Library Operating System

The library OS is a unikernel that is linked at compile-time with Selfie. Upon boot, the unikernel initializes the hardware and prepares an execution environment, before calling into Selfie's `main` function with compile-time arguments. After returning from `main` or calling `exit`, the kernel prints the exit code and stalls the system.

As the library OS is a simple layer between the hardware and Selfie, it does not utilize multitasking or memory virtualization. In a cooperative way, the kernel passes control to the linked application and regains control when Selfie performs a syscall. Selfie and the kernel are not spatially isolated  and both use physical addressing. System calls are plain function calls and do not raise an environment call exception.

The library OS does not install a trap handler. If Selfie or the kernel raise an exception, it will be handled by OpenSBI.

### Software Stack

| Privilege level | Software   |
| --------------- | ---------- |
| Machine mode    | OpenSBI    |
| Supervisor mode | Library OS |

## Multitasking Kernel

The multitasking kernel builds upon [RISC-V's privileged specification v1.11](https://riscv.org//wp-content/uploads/2019/08/riscv-privileged-20190608-1.pdf) but is compatible with implementations of [RISC-V's privileged specification v1.10](https://riscv.org//wp-content/uploads/2017/05/riscv-privileged-v1.10.pdf). This means that at the moment it is not possible to execute it on the Kendryte K210.

Special features include:
* Preemptive multitasking
* Round-robin scheduling
* Memory virtualization through the use of RISC-V's Sv39 paging
* Rudimentary trap handling including support for the five system calls `exit`, `read`, `write`, `openat`, and `brk`
* An ELF loader that is capable of loading ELF files emitted by Selfie

Details of this kernel's implementation are described in [Martin Fischer's bachelor thesis "RISC-V S-Mode-Hosted Bare-Metal Selfie"](../theses#risc-v-s-mode-hosted-bare-metal-selfie-by-martin-fischer-university-of-salzburg-austria-2020-pdf-release).

#### Software Stack

| Privilege level | Software       |
| --------------- | -------------- |
| Machine mode    | OpenSBI        |
| Supervisor mode | Kernel         |
| User mode       | User processes |

## Common Source Code

Both the library OS and kernel OS variant [share common code](./Makefile#L24) for:
- Kernel Bootstrapping
- Generalized init process bootstrapping
- Kernel C standard library
- Console
- SBI calls
- Static read-only File System
- Diagnostics
- Generalized system calls

Each kernel variant must provide implementations for concrete init process bootstrapping as well as glue code between the syscall interface and the generalized syscall implementation.

## Building Selfie For Bare Metal

Selfie's bare-metal support comes with a [separate Makefile](Makefile).

### Special Requirements

* `gcc-riscv64-linux-gnu`
* `binutils-riscv64-linux-gnu`

### Build Steps

Running `make` within the [`machine` directory](.) will download OpenSBI's v0.7 release and build both the library operating system and the multitasking kernel for all supported platforms. The resulting payloads are in the respective directories in the `build` directory.

#### Boards / Build Profiles

The Makefile refers to distinct hardware platforms as _boards_. Currently, three boards are supported:
- `qemu`: The QEMU virtual machine
- `fu540`: SiFive Freedom U540 ([HiFive Unleashed](https://www.sifive.com/boards/hifive-unleashed))
- `k210`: Kendryte K210

Also, the Makefile distinguishes between two _build profiles_:
- `library`: Targets the library OS
- `kernel`: Targets the multitasking kernel

#### Special Makefile targets

| **Target name**                      | **Description**                                                                              |
|--------------------------------------|----------------------------------------------------------------------------------------------|
| all (default)                        | Builds all board/build profile combinations                                                  |
| clean                                | Cleans all build artifacts, but retains opensbi                                              |
| distclean                            | Cleans all build artifacts and opensbi (requires re-download)                                |
| debug                                | Sets the debugging macro (i.e. adds `-DDEBUG` to compiler flags)                             |
| list-targets                         | Lists targets names of all board/build profile combinations                                  |
| selfie-\$board.elf                   | Builds all build profiles for the specified board as ELF file (without OpenSBI)              |
| selfie-\$board.bin                   | Builds all build profiles for the specified board as flat binary (without OpenSBI)           |
| selfie-opensbi-\$board.elf           | Builds all build profiles for the specified board as ELF file (with OpenSBI)                 |
| selfie-\$board-\$profile.elf         | Builds the specified build profiles for the specified board as ELF file (without OpenSBI)    |
| selfie-\$board-\$profile.bin         | Builds the specified build profiles for the specified board as flat binary (without OpenSBI) |
| selfie-opensbi-\$board-\$profile.elf | Builds the specified build profiles for the specified board as ELF file (with OpenSBI)       |
| test                                 | Builds QEMU `library` and `kernel` variants and tries to run them                            |
| opensbi                              | Fetches and extracts OpenSBI                                                                 |

The `debug` target may be used by prepending it to the target to build, e.g. `make debug all` to build all possible board/build profile combinations in debug mode. Switching between debug and non-debug builds requires to `clean` the build tree.

#### Build artifacts

The `build` directory contains all intermediate object files and linker scripts as well as the resulting binaries:

```
build
├── fu540
│   ├── kernel
│   │   ├── [...]
│   │   ├── selfie.bin
│   │   ├── selfie.elf
│   │   ├── selfie-opensbi.elf
│   │   └── [...]
│   └── library
│       ├── [..]
│       ├── selfie.bin
│       ├── selfie.elf
│       ├── selfie-opensbi.elf
│       └── [...]
:
```

`selfie.elf` is the main artifact that contains the kernel and the static file system. `selfie.bin` is the flat binary version of `selfie.elf` that must be loaded to \$SBI\_START+\$PAYLOAD\_OFFSET, as specified in the Makefile.

`selfie.elf` and `selfie.bin` do not contain OpenSBI which is required as supervisor binary. Therefore, it is necessary that the board's bootloader loads OpenSBI and the kernel.

`selfie-opensbi.elf` packages `selfie.bin` to OpenSBI using the `FW_PAYLOAD` Makefile configuration. Thus, it is an OpenSBI binary that passes execution to the `selfie.bin` payload after initialization. This is necessary for binaries that must be self-contained, mostly on embedded platforms.

> **:warning: Warning:** QEMU 5.1 behavoral changes
>
> QEMU v5.1+ [changed default behavior](https://wiki.qemu.org/ChangeLog/5.1#RISC-V) on `virt` and `sifive_u` RISC-V emulation machines to load OpenSBI 0.7 per default. To prevent two OpenSBI binaries from clashing, one of two options must be considered:
> - Use `selfie.elf` binary
> - Use `selfie-opensbi.elf` binary and prevent QEMU from loading the shipped OpenSBI using the `-bios none` flag
>
> Older QEMU versions do not load OpenSBI per default and require the `selfie-opensbi.elf` binary.
