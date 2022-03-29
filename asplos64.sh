# BASELINE (106 steps):
./beator -c s.c - 0 --heap-allowance 8 --stack-allowance 56
mv s.btor2 64fsm/baseline.btor2

# BASE-LIN (106 steps)
./beator -c s.c - 0 --heap-allowance 8 --stack-allowance 56 --linear-address-space
mv s.btor2 64fsm/base_lin.btor2

# BASE-MMU (106 steps):
./beator -c s.c - 0 --heap-allowance 8 --stack-allowance 56 --MMU
mv s.btor2 64fsm/base_mmu.btor2

# BASE-RAM (106 steps):
./beator -c s.c - 0 --heap-allowance 8 --stack-allowance 56 --RAM
mv s.btor2 64fsm/base_ram.btor2

# BASE-MR (106 steps):
./beator -c s.c - 0 --heap-allowance 8 --stack-allowance 56 --MMURAM
mv s.btor2 64fsm/base_mr.btor2

# CONST-PROP (37 steps):
./beator -c s.c - 0 --constant-propagation
mv s.btor2 64fsm/const_prop.btor2

# CONST-LIN (37 steps):
./beator -c s.c - 0 --constant-propagation --linear-address-space
mv s.btor2 64fsm/const_lin.btor2

# CONST-MMU (37 steps):
./beator -c s.c - 0 --constant-propagation --MMU
mv s.btor2 64fsm/const_mmu.btor2

# CONST-RAM (37 steps):
./beator -c s.c - 0 --constant-propagation --RAM
mv s.btor2 64fsm/const_ram.btor2

# CONST-MR (37 steps)
./beator -c s.c - 0 --constant-propagation --MMURAM
mv s.btor2 64fsm/const_mr.btor2

# 12BAD (106 steps):
./beator -c s.c - 0 --heap-allowance 8 --stack-allowance 56 --no-syscall-id-check --no-exit-code-check --no-division-by-zero-check --no-address-alignment-check
mv s.btor2 64fsm/12bad.btor2

# 12BAD-LIN (106 steps):
./beator -c s.c - 0 --heap-allowance 8 --stack-allowance 56 --no-syscall-id-check --no-exit-code-check --no-division-by-zero-check --no-address-alignment-check --linear-address-space
mv s.btor2 64fsm/12bad_lin.btor2

# 12BAD-MMU (106 steps):
./beator -c s.c - 0 --heap-allowance 8 --stack-allowance 56 --no-syscall-id-check --no-exit-code-check --no-division-by-zero-check --no-address-alignment-check --MMU
mv s.btor2 64fsm/12bad_mmu.btor2

# 12BAD-RAM (106 steps):
./beator -c s.c - 0 --heap-allowance 8 --stack-allowance 56 --no-syscall-id-check --no-exit-code-check --no-division-by-zero-check --no-address-alignment-check --RAM
mv s.btor2 64fsm/12bad_ram.btor2

# 12BAD-MR (106 steps):
./beator -c s.c - 0 --heap-allowance 8 --stack-allowance 56 --no-syscall-id-check --no-exit-code-check --no-division-by-zero-check --no-address-alignment-check --MMURAM
mv s.btor2 64fsm/12bad_mr.btor2

# 12BAD-CONST (37 steps):
./beator -c s.c - 0 --no-syscall-id-check --no-exit-code-check --no-division-by-zero-check --no-address-alignment-check --constant-propagation
mv s.btor2 64fsm/12bad_const.btor2

# 12BAD-C-LIN (37 steps):
./beator -c s.c - 0 --no-syscall-id-check --no-exit-code-check --no-division-by-zero-check --no-address-alignment-check --constant-propagation --linear-address-space
mv s.btor2 64fsm/12bad_c_lin.btor2

# 12BAD-C-MMU (37 steps):
./beator -c s.c - 0 --no-syscall-id-check --no-exit-code-check --no-division-by-zero-check --no-address-alignment-check --constant-propagation --MMU
mv s.btor2 64fsm/12bad_c_mmu.btor2

# 12BAD-C-RAM (37 steps):
./beator -c s.c - 0 --no-syscall-id-check --no-exit-code-check --no-division-by-zero-check --no-address-alignment-check --constant-propagation --RAM
mv s.btor2 64fsm/12bad_c_ram.btor2

# 12BAD-C-MR (37 steps):
./beator -c s.c - 0 --no-syscall-id-check --no-exit-code-check --no-division-by-zero-check --no-address-alignment-check --constant-propagation --MMURAM
mv s.btor2 64fsm/12bad_c_mr.btor2