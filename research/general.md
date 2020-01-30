# Wichtige Links
* [SiFive FU540 Manual](https://sifive.cdn.prismic.io/sifive%2F834354f0-08e6-423c-bf1f-0cb58ef14061_fu540-c000-v1.0.pdf) (SiFive HiFive Unleashed)
* [K210 Manual](https://s3.cn-north-1.amazonaws.com.cn/dl.kendryte.com/documents/kendryte_datasheet_20181011163248_en.pdf) (Sipeed Maix Bit)
* RISC-V ISA
	* [The RISC-V Instruction Set Manual Volume I: User-Level ISA](https://content.riscv.org/wp-content/uploads/2017/05/riscv-spec-v2.2.pdf)
	* [The RISC-V Instruction Set Manual Volume II: Privileged Architecture](https://content.riscv.org/wp-content/uploads/2019/08/riscv-privileged-20190608-1.pdf)
* [RISC-V OS construction guide](http://osblog.stephenmarz.com/index.html)
	* [Interrupt Handling](http://osblog.stephenmarz.com/ch4.html)

# Notizen

## Boot-Prozess
Der BBL wurde ersetzt durch OpenSBI (https://riscv.org/2019/01/risc-v-community-releases-opensbi-to-foster-continued-ecosystem-growth/)


## Interrupt handling
### Register
* `mtvec`-Register (Machine Trap Vector) speichert Pointer auf Funktion
	* `BASE`-Feld speichert die Adresse
	* `MODE`-Feld (2 Bit) speichert Modus -> `0` für Direct mode (leitet immer an die selbe Funktion weiter)
* `mcause`-Register (machine cause) beinhaltet Grund für Trap
	* Interrupt Bit: indiziert, ob der Interrupt asynchronous oder synchronous ausgelöst wurde
		* asynchronous (`1`): etwas anderes als die momentan ausgeführte Instruktion hat den Interrupt verursacht
		* synchronous (`0`): momentan ausgeführte Instruktion hat den Interrupt verursacht
