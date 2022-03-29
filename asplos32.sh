# This file is executed in a docker image under the command:
# docker run --platform linux/amd64 -it -v /path/to/local/selfie:/opt/myselfie cksystemsteaching/selfie

# 32-BASELINE (106 steps):
./beator-32 -c s.c - 0 --heap-allowance 4 --stack-allowance 28
mv s.btor2 32fsm/baseline.btor2

# 32-BASE-LIN (106 steps):
./beator-32 -c s.c - 0 --heap-allowance 4 --stack-allowance 28 --linear-address-space
mv s.btor2 32fsm/base_lin.btor2

# 32-BASE-MMU (106 steps):
./beator-32 -c s.c - 0 --heap-allowance 4 --stack-allowance 28 --MMU
mv s.btor2 32fsm/base_mmu.btor2

# 32-BASE-RAM (106 steps):
./beator-32 -c s.c - 0 --heap-allowance 4 --stack-allowance 28 --RAM
mv s.btor2 32fsm/base_ram.btor2

# 32-BASE-MR (106 steps):
./beator-32 -c s.c - 0 --heap-allowance 4 --stack-allowance 28 --MMURAM
mv s.btor2 32fsm/base_mr.btor2

# 32-CONST-PROP (37 steps):
./beator-32 -c s.c - 0 --constant-propagation
mv s.btor2 32fsm/const_prop.btor2

# 32-CONST-LIN (37 steps):
./beator-32 -c s.c - 0 --constant-propagation --linear-address-space
mv s.btor2 32fsm/const_lin.btor2

# 32-CONST-MMU (37 steps):
./beator-32 -c s.c - 0 --constant-propagation --MMU
mv s.btor2 32fsm/const_mmu.btor2

# 32-CONST-RAM (37 steps):
./beator-32 -c s.c - 0 --constant-propagation --RAM
mv s.btor2 32fsm/const_ram.btor2

# 32-CONST-MR (37 steps):
./beator-32 -c s.c - 0 --constant-propagation --MMURAM
mv s.btor2 32fsm/const_mr.btor2

# 32-12BAD (106 steps):
./beator-32 -c s.c - 0 --heap-allowance 4 --stack-allowance 28 --no-syscall-id-check --no-exit-code-check --no-division-by-zero-check --no-address-alignment-check
mv s.btor2 32fsm/12bad.btor2

# 32-12BAD-LIN (106 steps):
./beator-32 -c s.c - 0 --heap-allowance 4 --stack-allowance 28 --no-syscall-id-check --no-exit-code-check --no-division-by-zero-check --no-address-alignment-check --linear-address-space
mv s.btor2 32fsm/12bad_lin.btor2

# 32-12BAD-MMU (106 steps):
./beator-32 -c s.c - 0 --heap-allowance 4 --stack-allowance 28 --no-syscall-id-check --no-exit-code-check --no-division-by-zero-check --no-address-alignment-check --MMU
mv s.btor2 32fsm/12bad_mmu.btor2

# 32-12BAD-RAM (106 steps):
./beator-32 -c s.c - 0 --heap-allowance 4 --stack-allowance 28 --no-syscall-id-check --no-exit-code-check --no-division-by-zero-check --no-address-alignment-check --RAM
mv s.btor2 32fsm/12bad_ram.btor2

# 32-12BAD-MR (106 steps):
./beator-32 -c s.c - 0 --heap-allowance 4 --stack-allowance 28 --no-syscall-id-check --no-exit-code-check --no-division-by-zero-check --no-address-alignment-check --MMURAM
mv s.btor2 32fsm/12bad_mr.btor2

# 32-12BAD-CONST (37 steps):
./beator-32 -c s.c - 0 --no-syscall-id-check --no-exit-code-check --no-division-by-zero-check --no-address-alignment-check --constant-propagation
mv s.btor2 32fsm/12bad_const.btor2

# 32-12BAD-C-LIN (37 steps):
./beator-32 -c s.c - 0 --no-syscall-id-check --no-exit-code-check --no-division-by-zero-check --no-address-alignment-check --constant-propagation --linear-address-space
mv s.btor2 32fsm/12bad_c_lin.btor2

# 32-12BAD-C-MMU (37 steps):
./beator-32 -c s.c - 0 --no-syscall-id-check --no-exit-code-check --no-division-by-zero-check --no-address-alignment-check --constant-propagation --MMU
mv s.btor2 32fsm/12bad_c_mmu.btor2

# 32-12BAD-C-RAM (37 steps):
./beator-32 -c s.c - 0 --no-syscall-id-check --no-exit-code-check --no-division-by-zero-check --no-address-alignment-check --constant-propagation --RAM
mv s.btor2 32fsm/12bad_c_ram.btor2

# 32-12BAD-C-MR (37 steps):
./beator-32 -c s.c - 0 --no-syscall-id-check --no-exit-code-check --no-division-by-zero-check --no-address-alignment-check --constant-propagation --MMURAM
mv s.btor2 32fsm/12bad_c_mr.btor2