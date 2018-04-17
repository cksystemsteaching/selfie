uint64_t main () {
    uint64_t* s;
    s = malloc(24);

    read(0, s, 22); // [0, MAX], [0, MAX], [0, 2^48]

    if (*(s + 0) < 112)
        return 1;
    if (*(s + 1) < 223)
        return 2;
    if (*(s + 2) < 334)
        return 3;

    return 0;
}