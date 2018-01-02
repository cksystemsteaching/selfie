uint64_t c = 0;

uint64_t main(uint64_t argc, uint64_t *argv) {
    uint64_t a;
    uint64_t b;
    uint64_t* p;
    
    // simple addition
    a = 0;
    b = 1;
    c = a + b;

    // environment
    if (write(1, (uint64_t*) "hello world", 1) != 1) return -1; // write always works
    if (open((uint64_t*) "something.txt", 1, 1) != 5) return -1; // first fake file descriptor is 5
    p = malloc(8);
    read(1, p, 2);

    return *p + c;
}