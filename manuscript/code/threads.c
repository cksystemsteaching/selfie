void initialize();
void allocate(uint64_t* memory);
uint64_t check_race_condition();

uint64_t  NUMBER_OF_MALLOCS = 100;
uint64_t* MEMORY_CHILD;
uint64_t* MEMORY_PARENT;

void initialize() {
    MEMORY_CHILD  = malloc(NUMBER_OF_MALLOCS * 8);
    MEMORY_PARENT = malloc(NUMBER_OF_MALLOCS * 8);
}

void allocate(uint64_t* memory) {
    uint64_t i;

    i = 0;

    while (i < NUMBER_OF_MALLOCS) {
        *(memory + i) = (uint64_t) malloc(8);

        i = i + 1;
    }
}

uint64_t check_race_condition() {
    uint64_t i;
    uint64_t j;
    uint64_t rcs;

    i   = 0;
    rcs = 0;

    while (i < NUMBER_OF_MALLOCS) {
        j = 0;

        while (j < NUMBER_OF_MALLOCS) {
            // same address assigned -> race condition occurred
            if (*(MEMORY_CHILD + i) == *(MEMORY_PARENT + j))
                rcs = rcs + 1;

            j = j + 1;
        }

        i = i + 1;
    }

    return rcs;
}

uint64_t main() {
    uint64_t t_id;

    // initialize shared memory buffer
    initialize();

    t_id = thread();

    if (t_id == 0)
        allocate(MEMORY_CHILD);
    else {
        allocate(MEMORY_PARENT);
        wait();

        return check_race_condition();
    }

    return 0;
}