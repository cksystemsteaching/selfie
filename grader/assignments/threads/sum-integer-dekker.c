void* malloc(unsigned long);

uint64_t pthread_create();
uint64_t pthread_join(uint64_t* status);
void     pthread_exit(uint64_t status);

uint64_t  turn = 0;
uint64_t* wants_to_enter;
uint64_t  sum = 0;

void dekker_enter_critical_section(uint64_t my_turn_id) {
  uint64_t other_turn_id;

  if (my_turn_id == 0)
    other_turn_id = 1;
  else
    other_turn_id = 0;

  *(wants_to_enter + my_turn_id) = 1;
  while (*(wants_to_enter + other_turn_id) == 1) {
    if (turn != my_turn_id) {
      *(wants_to_enter + my_turn_id) = 0;
      while (turn != my_turn_id) {
        // We do not have a direct way to yield
        // Instead, perform a zero-sized read() to (hopefully) provoke a switch
        read(0, (uint64_t*) 0, 0);
      }
      *(wants_to_enter + my_turn_id) = 1;
    }
  }
}
void dekker_leave_critical_section(uint64_t my_turn_id) {
  uint64_t other_turn_id;

  if (my_turn_id == 0)
    other_turn_id = 1;
  else
    other_turn_id = 0;

  *(wants_to_enter + my_turn_id) = 0;
  turn = other_turn_id;
}

int main(int argc, char** argv) {
  uint64_t  tid;
  uint64_t* status;
  uint64_t  i;

  uint64_t  my_turn_id;
  uint64_t  other_turn_id;

  status = malloc(8);
  wants_to_enter = malloc(16);

  tid = pthread_create();

  if (tid)
    my_turn_id = 0;
  else
    my_turn_id = 1;

  dekker_enter_critical_section(my_turn_id);

  // The   main thread will sum up all  odd integers: 1, 3, 5, 7,  9, 11, 13, 15, 17, 19
  // The second thread will sum up all even integers: 2, 4, 6, 8, 10, 12, 14, 16, 18, 20
  while (i < 10) {
    sum = sum + (2*i + my_turn_id + 1);
    i = i + 1;
  }

  dekker_leave_critical_section(my_turn_id);


  if (tid)
    pthread_join(status);
  else
    pthread_exit(0);

  return sum;
}