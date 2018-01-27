uint64_t main() {
    uint64_t* p;
    p = malloc(8);
    read(0, p, 1); // symbolic [0, 255]

    // supports only < and >
    // also change branch in symbolic_do_beq
    if (100 > *p)
        return *p;

    return *p;
}