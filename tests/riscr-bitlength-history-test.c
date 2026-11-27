// The bit-length loop of projects/reversible.md as C* has it: it counts
// in c how often x can be halved, x being the byte it reads. riscr
// translates it with history: what an assignment overwrites, and a flag
// per iteration, see riscr.md.
//
// The same loop without history is tests/riscr-bitlength-test.c. The two
// from loops here never execute their bodies and leave no history: riscr
// reports where they are, which is where the loop begins and ends.
// For gcc, from(e) is defined as nothing.

uint64_t read(uint64_t fd, uint64_t* buffer, uint64_t bytes_to_read);

void* malloc(unsigned long);

uint64_t x; // the number
uint64_t c; // the number of its bits
uint64_t m; // zero

int main() {
  uint64_t* p;

  p = malloc(8);

  *p = 0;

  read(0, p, 1);

  x = *p;

  from (m == 0) while (m != 0) { }

  while (x != 0) {
    x = x / 2;

    c = c + 1;
  }

  from (m == 0) while (m != 0) { }

  return c;
}
