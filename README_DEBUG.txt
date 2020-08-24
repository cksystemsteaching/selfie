selfie.c
  mipster printed jetzt alle register vor jeder instruction
wipopt
  optimizer binary (x86)
enops.txt
  machine state vor jeder enop instruction + die instruction
states.txt
  liste des bekannten states an jeder instruction

debug_run.sh
  kompiliert alles und erstellt folgende files: (NICHT enops.txt und states.txt)

selfie.opt
  optimierte riscv selfie binary
selfie.s
  selfie disassembly
selfie.opt.s
  optimized selfie disassembly
selfie.rv
  riscv selfie binary
usage.txt
  alle register bei einer ausfuehrung von selfie ohne parameter (nur usage string printen)
usage.opt.txt
  alle register bei einer ausfuehrung von optimized selfie ohne parameter (nur usage string printen)
