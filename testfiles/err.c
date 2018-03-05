uint64_t main () {
    uint64_t* p;

    p = malloc(8);
    read(0, p, 1); // [0, 255]

    *p = *p + 5; // [5, 260]

    if (*p < 10) {// T: [5, 9] 
        *p = *p + 5; // [10, 14]

        if (*p >= 10) // T: [10, 14] V > [0, 4]
        return 666;
        else // F: [10, 9] X > [0, 0]
        return 555;

    } else // F: [10, 260] V > [5, 255]
        return 111; 

}