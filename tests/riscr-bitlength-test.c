// The bit-length loop of riscr.md, garbage-free: it counts
// in c how often x can be halved, x being the byte it reads. Halving x
// destroys the low bit of x, which this program keeps in s, a bit per
// iteration: that is all the information the loop destroys. All of its
// statements are compound assignments and its loop is a from loop, so
// riscr translates it without history, see riscr.md.
//
// The same loop with history is tests/riscr-bitlength-history-test.c.
// For gcc, from(e) is defined as nothing.

uint64_t read(uint64_t fd, uint64_t* buffer, uint64_t bytes_to_read);

void* malloc(unsigned long);

uint64_t x; // the number
uint64_t c; // the number of its bits
uint64_t s; // its bits, the lowest first
uint64_t t; // zero but in the body of the loop
uint64_t h; // zero but in the body of the loop
uint64_t u; // zero but in the body of the loop

int main() {
  uint64_t* p;

  p = malloc(8);

  *p = 0;

  read(0, p, 1);

  x += *p;

  from (c == 0) while (x != 0) {
    // the low bit of x
    t += x % 2;
    x -= t;

    // x becomes half of what it is, through h
    h += x / 2;
    x -= h;
    x -= h;
    x += h;
    h -= x;

    // s becomes twice what it is, through u, and gets the bit
    u += s;
    s += u;
    u -= s / 2;
    s += t;
    t -= s % 2;

    c += 1;
  }

  return c;
}
