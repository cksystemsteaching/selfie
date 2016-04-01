# 3. Architecture

## Von Neumann Architecture

![Von Neumann Architecture](images/von-neumann-architecture.jpg "Von Neumann Architecture")

{line-numbers=on, lang=c}
<<[A Simple C* Program](code/iteration.c)

{line-numbers=on, lang=c}
<<[Informal Semantics of the Simple C* Program](code/iteration-low.c)

{line-numbers=on, lang=c}
<<[Language Elements of the Simple C* Program](code/iteration-high.c)

{line-numbers=off, lang=asm}
<<[Formal Semantics of the Simple C* Program in MIPS Assembly with Approximate Line Numbers](code/iteration.s)

{line-numbers=off, lang=asm}
<<[Execution of the MIPS Assembly for the Simple C* Program with Approximate Line Numbers and Profile](code/iteration.d)

{line-numbers=on, lang=c}
<<[A C* Program Equivalent to the Simple C* Program](code/procedure.c)

{line-numbers=off, lang=asm}
<<[Formal Semantics of the Equivalent C* Program in MIPS Assembly with Approximate Line Numbers](code/procedure.s)

{line-numbers=on, lang=c}
<<[A C* Program Equivalent to the Simple C* Program Using a Function](code/function.c)

{line-numbers=off, lang=asm}
<<[Formal Semantics of the Equivalent C* Program Using a Function in MIPS Assembly with Approximate Line Numbers](code/function.s)