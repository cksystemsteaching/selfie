uint64_t twoPow56 = 72057594037927936;
uint64_t twoPow48 = 281474976710656;

uint64_t main () {
    uint64_t * s;
    uint64_t * t;
    s = malloc(8);
    t = malloc(8);
    read(0, s, 2);
    *t = 25185;
    
    if ((*s * twoPow56) / twoPow56 == 'a'){
        if ((*s * twoPow48) / twoPow56 == 'b') {
            return 666; // reachable with [25185, 25185]
        }
    }

    return 0;
}