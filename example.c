uint64_t a(uint64_t b) {
    uint64_t a;
    a = 1 + b;
    return a;
}

void b() {
    uint64_t b;
    b = 1;
}

uint64_t main(uint64_t argc, uint64_t* argv) {
    uint64_t i;
    i = 1;
    i = a(1);
    i = 2;
    b();
    i = 3;
    return 0;
}