uint64_t COUNT = 300;
uint64_t* array;

uint64_t SIZEOFUINT64 = 8; // must be the same as REGISTERSIZE

void swap(uint64_t* xp, uint64_t* yp) {
  uint64_t temp;

  temp  = *(xp);
  *(xp) = *(yp);
  *(yp) = temp;
}

void selection_sort(uint64_t* arr, uint64_t n) {
  uint64_t i;
  uint64_t j;
  uint64_t min_idx;

  i = 0;
  while (i < n - 1) {
    min_idx = i;
    j = i + 1;
    while (j < n) {
      if (*(arr + j) < *(arr + min_idx))
        min_idx = j;
      j = j + 1;
    }

    swap(arr + min_idx, arr + i);
    i = i + 1;
  }
}

uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t i;
  array = malloc(COUNT * SIZEOFUINT64);

  i = 0;
  while (i < COUNT - 1) {
    *(array + i) = COUNT - i;
    i = i + 1;
  }

  //klee_assume(arr[count-1] < 5*count);
  //klee_assume(arr[count-1] > 0);
  *(array + (COUNT - 1)) = input(0, 5*COUNT, 1);
  selection_sort(array, COUNT);

  return 0;
}
