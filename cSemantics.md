# backwards constraining semantics
```c
pc  // program counter

tc  // current trace counter
btc // trace counter for moving backwards in the trace
    .pcs // pc in trace
    .tcs // old tc in trace
    .upper // upper value in trace
    .lower // lower value in trace
```

## ADDI
### ADDI forwards
```c
tc.pcs = pc // current pc
tc.tcs = rd // old tc

tc.upper = rs1.upper + imm
tc.lower = rs1.lower + imm
pc++

rd = tc
tc++
```

### cADDI backwards
```c
tc.pcs = pc // current pc
tc.tcs = rs1 // old forward tc

if (rd == rs1) { // constraint rd/rs1
    tc.upper = rd.upper - imm
    tc.lower = rd.lower - imm
} else { // constraint rs1 / restore old rd
    tc.upper = rd.upper - imm
    tc.lower = rd.lower - imm
    rd = btc.tcs // old backwards tc
}
pc--

rs1 = tc
tc++
btc--
```

## ADD
### ADD forwards
```c
tc.pcs = pc // current pc
tc.tcs = rd // old tc

tc.upper = rs1.upper + rs2.upper
tc.lower = rs1.lower + rs2.lower
pc++

rd = tc
tc++
```

### cADD backwards
```c
tc.pcs = pc // current pc

if (bothConcrete) { // restore old rd
    tc.tcs = rd // old forward tc
    if (rd == rs1) rd = btc.tcs // old backwards tc
    else if (rd == rs2) rd = btc.tcs // old backwards tc
    else rd = btc.tcs // old backwards tc
    // we don't need to store the current tc
} else if (oneConcrete) {
    // find symReg, conReg (MAGIC)
    if (symReg == rd) {
        tc.tcs = symReg // old forward tc
        tc.upper = rd.upper - con.upper
        tc.lower = rd.lower - con.lower
        symReg = tc
    } else if (conReg == rd) {
        // constraint symbolic reg anyway
        tc.tcs = symReg // old forward tc
        tc.upper = rd.upper - con.upper
        tc.lower = rd.lower - con.lower
        symReg = tc
        rd = btc.tcs // old backwards tc
    } else {
        tc.tcs = symReg // old forward tc
        tc.upper = rd.upper - con.upper
        tc.lower = rd.lower - con.lower
        symReg = tc
        rd = btc.tcs // old backwards tc
    }
} else {
    // both are symbolic - what do we constrain?
}

pc--
tc++
btc--
```

## LD
### LD forwards
```c
tc.pcs = pc // current pc
tc.tcs = rd // old tc

vaddr = rs1.lower + imm
tc.upper = load(vaddr).upper
tc.lower = load(vaddr).lower
pc++

rd = tc
tc++
```

### sLD backwards
```c
if (rs1 == rd) {
    vaddr = btc.lower // get old address
} else {
    vaddr = rs1.lower + imm
}
// get respective tcs
mem_tc = load(vaddr)
reg_tc = rd

if (!sameIntervalls(mem_tc, reg_tc)) { // do we have a newer value in memory?
    tc.pcs = pc // current pc
    tc.tcs = load(vaddr) // previous forward tc

    if (mem_tc.lower < reg_tc.lower) { // reg value more constrained
        tc.lower = reg_tc.lower
    } else { // mem value more constrained
        tc.lower = mem_tc.lower
    }

    if (mem_tc.upper > reg_tc.upper) { // reg value more constrained
        tc.upper = reg_tc.upper
    } else { // mem value more constrained
        tc.upper = reg_tc.upper
    }

    load(vaddr) = tc
    tc++
}

tc.pcs = pc // current pc
tc.tcs = rd // previous forward tc


tc.pcs = pc // current pc
tc.tcs = load(vaddr) // old forward tc

rd = btc.tcs // old backward tc
tc++
pc--
btc--
```

## SW
### SW forwards
```c
vaddr = rs1.lower + imm
tc.pcs = pc // current pc
tc.tcs = load(vaddr) // old tc

tc.upper = rs2.upper
tc.lower = rs2.lower
pc++

load(vaddr) = tc
tc++
```

### sSW backwards
```c
vaddr = rs1.lower + imm
tc.pcs = pc // current pc
tc.tcs = rs2 // old forward tc

tc.upper = load(vaddr).upper
tc.lower = load(vaddr).lower
load(vaddr) = btc.tcs // old backwards tc
pc--

rs2 = tc
tc++
btc--
```

## SLTU
### SLTU forwards
```c
tc.pcs = pc // current pc
tc.tcs = rd // old forward tc

if (rs1.upper < rs2.lower) {
    tc.upper = 1
    tc.lower = 1
} else if (rs1.lower >= rs2.upper) {
    tc.upper = 0
    tc.lower = 0
} else {
    tc.lower = 0
    tc.upper = 1
    // [0,1]
}

pc++
rd = tc
tc++
```

### cSLTU backwards
```c
if (rd.upper != rd.lower) {
    // [0,1] symbolic
    tc.pcs = pc // current pc
    tc.tcs = rd // old forward tc

    // sTODO

} else {
    tc.pcs = pc // current pc
    tc.tcs = rd // old forward tc
    rd = btc.tcs // old backwards tc
    tc++
    btc--
}
```

## BEQ
### BEQ forward
```c
tc.pcs = pc // current pc
tc.tcs = 0 // old forward tc

if (bothConcrete) {
    if (rs1.lower == rs2.lower)
        pc += imm
    else
        pc++
} else {
    if (branch)
        pc++
    else 
        pc += imm
}

tc++
```

### sBEQ backwards
```c
btc--
```
