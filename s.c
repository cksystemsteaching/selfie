uint64_t* x;
uint64_t main() {
    uint64_t a;
    x = malloc(1); // rounded up to 8
    // touch to trigger page fault here
    *x = 0;
    // read 1 byte from console into x
    read(0, x, 1);
    // copy from heap to stack segment
    a = *x;
    // decrement input until <= '0'
    while (a > '0')
        a = a - 1;
    // segmentation fault on input '1'
    if (a == *x - 1) // '0' == '1' - 1
        // segfault: '0' != 0
        a = *(x + a);
    return 0;
}