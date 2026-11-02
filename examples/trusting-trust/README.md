# Trusting trust: a compiler trojan and how to catch it

This is a self-contained, machine-checked lesson on Ken Thompson's
*Reflections on Trusting Trust* (1984) and David A. Wheeler's defence,
*diverse double-compiling* (DDC, 2005/2009), built on selfie.

Run it:

```
make trust
```

The target fails loudly if any step does not hold, so the lesson is a
check a machine runs, not a claim.

## The compiler

`stamp.c` is an honest **source-to-source compiler** for C\*: it reads a
C\* file and writes it out unchanged. The identity transform is still a
real compiler, and because its source language (C\*) is also the language
it is written in, it can compile its own source. That is the only property
Thompson's argument needs.

An honest `stamp` is a **fixed point**: `stamp` applied to `stamp.c`
produces `stamp.c` again, byte for byte (step 1 of `make trust`).

## The trojan

`stamp-trojan.c` is identical to `stamp.c` except for `emit_line`. Its
binary does two things no source it compiles ever asks for:

1. **Injection.** When it compiles `victim.c` it rewrites the exit-code
   line, so the compiled victim exits **42** although `victim.c` says `0`
   (steps 2 and 3). The 42 is an inert marker: the point is only that a
   compiler can add behaviour absent from the source. It is deliberately
   not a backdoor.

2. **Self-reproduction.** When it compiles the *clean* `stamp.c` it
   rewrites stamp's honest marker line into the trojaned one, so compiling
   clean source still yields a trojaned compiler. The honest compiler is a
   fixed point; the trojan is not.

Property 2 is Thompson's punch line: delete the trojan's source and keep
only its binary, and the trojan still reappears every time the binary
compiles the clean compiler. The malice lives in the binary, visible in no
source.

## Catching it with diverse double-compiling

You are handed a suspect compiler binary and told "this is the honest
`stamp.c`." You do not trust that. DDC checks it without reading the
binary:

- Compile the claimed source `stamp.c` on an **independent, trusted** path
  (here, the honest `stamp`). Call the result the honest output.
- Run the **suspect** on the same clean `stamp.c`. Call that the suspect
  output.
- Compare the two outputs.

The honest compiler reproduces `stamp.c` exactly; the trojan rewrites the
marker line, so the outputs differ (step 4). The suspect does not
faithfully implement the source it claims to be built from — detected,
with the clean source as the only input. A Thompson trojan survives only
by hiding in *every* independent compiler used as the trusted path, which
is the point of making the path diverse (a different host, a different
compiler, a different ISA).

## What this demo simplifies

The trojan here reproduces itself at the level of one **marker line**, not
its entire logic, so the files stay small and legible. A production
Thompson trojan reproduces its whole body; `examples/quine.c` shows the
exact self-reproduction that would carry it. The **detection** is identical
either way: DDC compares the suspect's output for the clean source against
an independent compiler's output for that same source, and any divergence
is the trojan.

Two preconditions, true here and worth stating:

- **Deterministic output.** The compiler's output must depend only on its
  input, not on timestamps, host, or memory layout. Selfie meets this;
  running DDC on two different hosts or ISAs also checks it.
- **An independent trusted path.** "Trusted" means independent of the
  suspect. DDC proves the binary matches its source up to the honesty of
  the compiler used as the trusted path; it does not prove the source
  itself is benign.

## Files

| File | Role |
| --- | --- |
| `stamp.c` | the honest identity compiler for C\*; a fixed point on its own source |
| `stamp-trojan.c` | the trojan: injects into the victim, re-trojans the clean compiler |
| `victim.c` | returns 0 in its source; exits 42 when built by the trojan |
| `README.md` | this file |

All three C\* files compile with both selfie and gcc (using `selfie.h` as
their library) and run on mipster, like selfie's other tools.

## References

- Ken Thompson, *Reflections on Trusting Trust*, Communications of the ACM,
  1984.
- David A. Wheeler, *Countering Trusting Trust through Diverse
  Double-Compiling*, ACSAC 2005, and his 2009 dissertation.
