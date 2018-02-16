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
tc.lower = rs1.lower + rs2.upper
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
        tc.lower = rd.lower - con.upper
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
vaddr = rs1.lower + imm
tc.pcs = pc // current pc
tc.tcs = load(vaddr) // old forward tc

tc.upper = rd.upper
tc.lower = tc.lower
rd = btc.tcs // old backwards tc
pc--

load(vaddr) = tc
tc++
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