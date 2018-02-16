uint64_t main() {
    uint64_t* p;
    uint64_t r;
    uint64_t c;

    c = 24;

    p = malloc(8);
    read(0, p, 1); // symbolic [0, 255]

    // supports only < and >
    // also change branch in symbolic_do_beq
    if (100 > *p)
        return *p;

    *p = *p + 12;
    //*p = *p * 2;
    r = *p;
    //r = r - c;

    return r;
}
