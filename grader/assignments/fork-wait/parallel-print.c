void* malloc(unsigned long);
void exit(int exit_code);
uint64_t write(uint64_t fd, uint64_t* buffer, uint64_t bytes_to_write);

uint64_t fork();
uint64_t wait(uint64_t* wstatus);

uint64_t sizeof_uint64 = 8;
uint64_t number_of_forks = 3;
uint64_t number_of_processes = 8; // 2 ^ #forks

// array of pids for a certain execution tree depth
uint64_t* pids;

// array with some numbers to be printed
uint64_t* sorted_numbers;

uint64_t intToAscii(uint64_t i) { return i + 48; }

// create a string with 8 times the ascii character for the number n
uint64_t toStringWithSpace(uint64_t n) {
  // assert: 0 <= n <= 9

  uint64_t i;
  uint64_t result;

  return 32 * 256 + intToAscii(n);
}

uint64_t i_am_parent(uint64_t depth) {
  return *(pids + depth) != 0;
}

// computes the process identity which is given by the execution tree
// every process can uniquely be identified by the sequence of PIDs received from fork()
// for example:
//  - the process with the saved PIDs (0, 0, 0) is the most outer leaf at the end
//  - the process with the saved PIDs (0, n, 0) is the 6. leaf counted from the start (with n > 0)
uint64_t who_am_i(uint64_t depth, uint64_t start, uint64_t end) {
  uint64_t mid;

  mid = (end - start) / 2 + start;

  if (start >= end - 1)
    return start;
  else if (i_am_parent(depth))
    return who_am_i(depth + 1, start, mid);
  else
    return who_am_i(depth + 1, mid, end);
}

void parallel_print(uint64_t depth) {
  uint64_t process_identity;

  if (depth == number_of_forks) {
    // determines which data element of the sorted_number
    // array will be printed by this process
    process_identity = who_am_i(0, 0, number_of_processes);

    write(1, sorted_numbers + process_identity, 2);
  } else {
    // save process id for a specific depth
    *(pids + depth) = fork();

    // parallel_print here is called 2 times
    parallel_print(depth + 1);

    // wait for the forked child
    if (i_am_parent(depth))
      wait(0);
    else
      exit(0);
  }
}

int main(int argc, char** argv) {
  uint64_t i;

  pids = malloc(sizeof_uint64 * number_of_forks);

  sorted_numbers = malloc(sizeof_uint64 * number_of_processes);

  // prepare data to be printed
  i = 0;
  while (i < number_of_processes) {
    *(sorted_numbers + i) = toStringWithSpace(i);

    i = i + 1;
  }

  parallel_print(0);

  write(1, (uint64_t*) "\n", 1);
}