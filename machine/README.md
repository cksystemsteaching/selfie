# Selfie Bare-Metal Support

Selfie features bare-metal support in the form of a library operating system and a multitasking kernel. Both of them include the same rudiumentary filesystem that is constructed during compile-time and are able to execute programs written in C\*. They are built upon an implementation of [RISC-V's Supervisor Binary Interface](https://github.com/riscv/riscv-sbi-doc/) in the form of [OpenSBI](https://github.com/riscv/opensbi/) v0.7. Supported platforms are [QEMU](https://www.qemu.org/) v5.0, the [SiFive HiFive Unleashed](https://www.sifive.com/boards/hifive-unleashed), and the [Kendryte K210](https://canaan.io/product/kendryteai).

## Library Operating System



## Multitasking Kernel

The multitasking kernel builds upon [RISC-V's privileged specification v1.11](https://riscv.org//wp-content/uploads/2019/08/riscv-privileged-20190608-1.pdf) but is compatible with implementations of [RISC-V's privileged specification v1.10](https://riscv.org//wp-content/uploads/2017/05/riscv-privileged-v1.10.pdf). This means that at the moment it is not possible to execute it on the Kendryte K210.

Special features include:
* Multitasking
* Round-robin scheduling
* Memory virtualization through the use of RISC-V's Sv39 paging

Details of this kernel's implementation are described in [Martin Fischer's bachelor thesis "RISC-V S-Mode-Hosted Bare-Metal Selfie"](../theses#risc-v-s-mode-hosted-bare-metal-selfie-by-martin-fischer-university-of-salzburg-austria-2020-pdf-release).

#### Software Stack

| Privilege level | Software       |
| --------------- | -------------- |
| Machine mode    | OpenSBI        |
| Supervisor mode | Kernel         |
| User mode       | User processes |

## Building Selfie For Bare Metal

Selfie's bare-metal support comes with a [separate Makefile](Makefile).

### Special Requirements

* `gcc-riscv64-linux-gnu`
* `binutils-riscv64-linux-gnu`

### Build Steps

Running `make` within the [`machine` directory](.) will download OpenSBI's v0.7 release and build both the library operating system and the multitasking kernel for all supported platforms. The resulting payloads are in the respective directories in the `build` directory.
