uint64_t twoToThePowerOf(uint64_t a) {
    if (a < 1) {
        return 1;
    } else return 2 * twoToThePowerOf(a-1);
}

uint64_t leftShift(uint64_t n, uint64_t b) {
  return n * twoToThePowerOf(b);
}

uint64_t rightShift(uint64_t n, uint64_t b) {
  return n / twoToThePowerOf(b);
}

uint64_t getChar(uint64_t * from, uint64_t at) { 
    uint64_t idx;
    uint64_t pos;

    idx = at / 8;
    pos = at % 8;

    return rightShift(leftShift(*(from + idx), 64 - ((pos * 8) + 8)), 56);
}

uint64_t main () {
    uint64_t * s;
    s = malloc(16);
    read(0, s, 16);
    
    if (getChar(s, 0) == 'a'){
        if (getChar(s, 8) == 'b') {
            return 666;
        }
    }

    return 0;
}