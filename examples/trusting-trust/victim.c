// trusting-trust: the victim program.
//
// Its source returns exit code 0. Compiled by an honest compiler it
// exits 0. Compiled by the trojaned "stamp" compiler (stamp-trojan.c)
// it exits 42 instead, a behavior that appears nowhere in this source.
//
// This is the payload half of Ken Thompson's "Reflections on Trusting
// Trust". The marker 42 is inert: it demonstrates that a compiler can
// inject behavior absent from the source, without being an attack.
//
// See README.md for the whole lesson.

uint64_t main() {
  return 0; // trusting-trust-victim
}
