# FU540 JTAG debugging

Using the latest riscv-openocd, it is possible to use the on-chip debugger of the FU540, used in the HiFive Unleashed.

For this to work, a Micro USB cable and the power brick is required.

OpenOCD hosts a GDB remote debugging server on localhost port 3333. Thus, it is possible to 
attach to the chip using `target extended-remote :3333`.

It seems like it is necessary to let OpenSBI run on the first core first, otherwise loading on all other chips does not seem to work.

```
break main
continue
```
After a few seconds, the core should hang in `sbi_hart_hang`. It is now possible to switch to a different HART using `thread [n]`, `load` the file and `continue` execution. Sometimes it takes a few tries.

Unfortunately, after a while, stepping or breakpoints do not work anymore. The only way to work around this is to switch to an unused HART or to restart OpenOCD


## Configuration files

### Configuration for OpenOCD
```
adapter_khz     10000

interface ftdi
ftdi_device_desc "Dual RS232-HS"
ftdi_vid_pid 0x0403 0x6010

ftdi_layout_init 0x0008 0x001b
ftdi_layout_signal nSRST -oe 0x0020

set _CHIPNAME riscv
jtag newtap $_CHIPNAME cpu -irlen 5 -expected-id 0x20000913

set _TARGETNAME_0 $_CHIPNAME.cpu0
set _TARGETNAME_1 $_CHIPNAME.cpu1
set _TARGETNAME_2 $_CHIPNAME.cpu2
set _TARGETNAME_3 $_CHIPNAME.cpu3
set _TARGETNAME_4 $_CHIPNAME.cpu4
target create $_TARGETNAME_0 riscv -chain-position $_CHIPNAME.cpu -rtos hwthread
target create $_TARGETNAME_1 riscv -chain-position $_CHIPNAME.cpu -coreid 1
target create $_TARGETNAME_2 riscv -chain-position $_CHIPNAME.cpu -coreid 2
target create $_TARGETNAME_3 riscv -chain-position $_CHIPNAME.cpu -coreid 3
target create $_TARGETNAME_4 riscv -chain-position $_CHIPNAME.cpu -coreid 4
target smp $_TARGETNAME_0 $_TARGETNAME_1 $_TARGETNAME_2 $_TARGETNAME_3 $_TARGETNAME_4

#set _TARGETNAME_0 $_CHIPNAME.cpu
#target create $_TARGETNAME_0 riscv -chain-position $_TARGETNAME_0 -rtos riscv

$_TARGETNAME_0 configure -work-area-phys 0x80000000 -work-area-size 10000 -work-area-backup 1


gdb_report_data_abort enable
gdb_report_register_access_error enable

# Expose an unimplemented CSR so we can test non-existent register access
# behavior.
riscv expose_csrs 2288

#>>>
reset_config trst_and_srst
adapter_nsrst_assert_width 100
#<<<

flash bank onboard_spi_flash fespi 0x20000000 0 0 0 $_TARGETNAME_0 0x10040000
init

# Clear reset on these events, because that messes with memory which we don't
# want in these tests. We want gdb be able to "download" to flash as well as
# RAM, and then simply execute the program.
# This must happen after init, where blank events get overwritten with reset.
set targets [target names]
foreach t $targets {
    $t configure -event gdb-flash-erase-start ""
    $t configure -event gdb-flash-write-end ""
}

reset

halt

# Uncomment this if you want to be able to clobber your SPI Flash, which
# probably you don't since you can do it through Linux
#flash protect 0 0 last off

echo "Ready for Remote Connections"
```

### Example GDB init file
```
target extended-remote :3333
file ../opensbi/build/platform/sifive/fu540/firmware/fw_payload.elf
add-symbol-file ./qemu-payload.elf
load
break main
```
