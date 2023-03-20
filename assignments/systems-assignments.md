# Systems Assignments

## The following information is shared via the course's slack channel.

- Lectures and tutorials
- Recordings
- Submitting homework
- Class schedule

## Important:

Always submit something for each assignment by the due date and time, even if you have not done anything. In that case, your self-grade is 5. If you fail to submit anything on time you will be failed (unless you provide proof of a medical or family emergency in a DM to me, no email please!).

## Essential for every assignment

Use the autograder to determine your grade. See the autograder's [README.md](../grader/README.md) for instructions.

> No compiler warnings, please!

## Assignment `print-your-name`:

Modify **selfie.c** such that selfie prints your name right after initialization.
Part of the assignment is to figure out how to do that.

- Do not modify any files other than **selfie.c**.
- Use the `print-your-name` target in the grader to determine your grade.

**Hint**: [output_processing.py](../grader/lib/output_processing.py)

Your message has to be prefixed like every other "status message" of selfie.
So instead of printing:

`This is <firstname> <lastname>'s Selfie!`, you have to print `<selfie-path>: This is <firstname> <lastname>'s Selfie!`



## Assignment `assembler-parser`:

Implement the parser of a RISC-U assembler invoked by option `-a` in selfie.

- Use the `assembler-parser` target in the grader to determine your grade.



## Assignment `self-assembler`:

Complete the implementation of a RISC-U assembler (option `-a` in selfie) with support of code generation.

- Use the `self-assembler` target in the grader to determine your grade.



## Assignment `processes`:

Implement support of processes in mipster and hypster.

- Use the `processes` target in the grader to determine your grade.



## Assignment `fork-wait`:

Implement support of `fork` and `wait` (for now with an unused dummy status argument) in mipster and hypster.

- Use the `fork-wait` target in the grader to determine your grade.



## Assignment `fork-wait-exit`:

Implement support of `fork` and `wait` with proper support of the status and exit code parameters in mipster and hypster.

- Use the `fork-wait-exit` target in the grader to determine your grade.



## Assignment `lock`:

Implement support of locking (`lock()` and `unlock()`).

- Use the `lock` target in the grader to determine your grade.



## Assignment `threads`:

Implement support of threads (`phtread_create()`, `pthread_join()`, and `pthread_exit()`).

- Use the `threads` target in the grader to determine your grade.



## Assignment `threadsafe-malloc`:

Make the current `malloc()` implementation thread-safe by implementing support of and using the atomic instructions `lr` and `sc` in RISC-U. This requires implementing support of load-reserved and store-conditional routines as well (`lr()` and `sc()`).

- Use the `threadsafe-malloc` target in the grader to determine your grade.



## Assignment `treiber-stack`:

Implement support of the Treiber stack (`init_stack()`, `push()`, and `pop()`).

- Use the `treiber-stack` target in the grader to determine your grade.


