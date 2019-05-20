uint64_t COUNT = 300;
uint64_t* array;

uint64_t SIZEOFUINT64 = 8; // must be the same as REGISTERSIZE
uint64_t INT64_MAX    = 9223372036854775807;
uint64_t INT64_MIN    = 9223372036854775808;

uint64_t signed_less_than(uint64_t a, uint64_t b) {
  return a + INT64_MIN < b + INT64_MIN;
}

void swap(uint64_t* xp, uint64_t* yp) {
  uint64_t temp;

  temp  = *(xp);
  *(xp) = *(yp);
  *(yp) = temp;
}

uint64_t partition(uint64_t* arr, uint64_t low, uint64_t high) {
  uint64_t pivot;
  uint64_t i;
  uint64_t j;

  pivot = *(arr + high);
  i     = low - 1;

  j = low;
  while (j < high) {
    if (*(arr + j) <= pivot) {
        i = i + 1;
        swap(arr + i, arr + j);
    }
    j = j + 1;
  }

  swap(arr + (i + 1), arr + high);
  return i + 1;
}

void quick_sort(uint64_t* arr, uint64_t low, uint64_t high) {
  uint64_t pi;

  if (signed_less_than(low, high)) {
    pi = partition(arr, low, high);
    quick_sort(arr, low, pi - 1);
    quick_sort(arr, pi + 1, high);
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
  quick_sort(array, 0, COUNT - 1);

  return 0;
}
