uint64_t * labyrinth;
uint64_t * LF;

uint64_t steps = 1;
uint64_t dimX = 3;
uint64_t dimY = 4;
uint64_t curX = 1;
uint64_t curY = 1;

void initLabyrinth () {
    labyrinth = malloc(8 * dimY);
    LF = malloc(8);

    *(labyrinth + 0) = (uint64_t) "###";
    *(labyrinth + 1) = (uint64_t) "#X#";
    *(labyrinth + 2) = (uint64_t) "#O#";
    *(labyrinth + 3) = (uint64_t) "###";
    *LF = 10; // new line
}

uint64_t twoToThePowerOf (uint64_t a) {
    if (a < 1) return 1;
    else return 2 * twoToThePowerOf(a-1);
}

uint64_t leftShift (uint64_t n, uint64_t b) { return n * twoToThePowerOf(b); }
uint64_t rightShift (uint64_t n, uint64_t b) { return n / twoToThePowerOf(b); }

uint64_t getChar (uint64_t * from, uint64_t at) { 
    uint64_t idx;
    uint64_t pos;
    idx = at / 8;
    pos = at % 8;
    return rightShift(leftShift(*(from + idx), 64 - ((pos * 8) + 8)), 56);
}

void printLab () {
    uint64_t i;
    i = 0;
    while (i < dimY) {
        write(0, *(labyrinth + i), dimX); write(0, LF, 1);
        i = i + 1;
    }
}

void checkWin () {
    uint64_t c;
    if (curX >= dimX) exit(-1);
    if (curY >= dimY) exit(-1);
    c = getChar(*(labyrinth + curY), curX);
    if (c == '#') exit(-1);
    else if (c == 'O') exit(0);

}

uint64_t main () {
    uint64_t * input;
    uint64_t i;
    uint64_t c;
    i = 0;

    initLabyrinth();
    // printLab();
    // write(0, "get from X to 0", 15); write(0, LF, 1);

    input = malloc(steps);
    read(0, input, steps);

    while (i < steps) {
        c = getChar(input, i);
        if (c == 's')
            curY = curY + 1;
        else if (c == 'a')
            curX = curX - 1;
        else if (c == 'd')
            curX = curX + 1;
        else if (c == 'w')
            curY = curY - 1;
        
        checkWin();
        i = i + 1;
    }

    return -1;
}