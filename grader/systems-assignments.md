# Systems Assignments

## This information is shared via the course's slack channel.

- Lectures and tutorials
- Recordings
- Submitting homework
- Class schedule



## Important:

Always submit something for any assignment by the due date and time, even if you have not done anything.
In that case, your self-grade is 5. If you fail to submit anything on time you will be failed (unless you provide proof of a medical or family emergency in a DM to me, no email please!).



## Essential for every assignment.

Use the autograder to determine your grade. See the grader [README.md](https://github.com/cksystemsteaching/selfie/blob/master/grader/README.md) file for instructions.

> No compiler warnings, please!



## Assignment `print-your-name`:

Modify **selfie.c** such that selfie prints your name right after initialization.
Part of the assignment is to figure out how to do that.

- Do not modify any files other than **selfie.c**.
- Use the `print-your-name` target in the grader to determine your grade.

**Hint**: [output_processing.py](https://github.com/cksystemsteaching/selfie/blob/e5b752478f774a384ab6ebd382acc6bdad0ea5df/grader/lib/output_processing.py#L8)

Your message has to be prefixed like every other "status message" of selfie.
So instead of printing: 

`This is <firstname> <lastname>'s Selfie!`, you have to print `<selfie-path>: This is <firstname> <lastname>'s Selfie!`



## Assignment `processes`:

Implement support of concurrent machines (processes) in mipster and hypster.

- Use the (concurrent-machines) `processes` target in the grader to determine your grade.



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



## Assignment `treiber-stack`:

TODO: Add description 

## Assignment `assembler-parser`:

TODO: Add description 

## Assignment `self-assembler`:

TODO: Add description 
