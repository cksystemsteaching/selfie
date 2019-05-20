uint64_t COUNT = 600;
uint64_t* array;
uint64_t SIZEOFUINT64 = 8; // must be the same as REGISTERSIZE
uint64_t INT64_MAX    = 9223372036854775807;
uint64_t INT64_MIN    = 9223372036854775808;

uint64_t signed_greater_than(uint64_t a, uint64_t b) {
  // INT64_MIN <= n <= INT64_MAX iff
  // INT64_MIN + INT64_MIN <= n + INT64_MIN <= INT64_MAX + INT64_MIN iff
  // -2^64 <= n + INT64_MIN <= 2^64 - 1 (sign-extended to 65 bits) iff
  // 0 <= n + INT64_MIN <= UINT64_MAX
  return a + INT64_MIN >= b + INT64_MIN;
}

uint64_t loop_condition(uint64_t j, uint64_t key, uint64_t* arr) {
  if (signed_greater_than(j, 0))
   if (*(arr + j) > key)
    return 1;
  return 0;
}

void insertion_sort(uint64_t* arr, uint64_t n) {
   uint64_t i;
   uint64_t key;
   uint64_t j;

   i = 1;
   while (i < n) {
       key = *(arr + i);
       j = i - 1;

      // Move elements of arr[0..i-1], that are
      // greater than key, to one position ahead
      // of their current position.
       while (loop_condition(j, key, arr)) {
           *(arr + (j + 1)) = *(arr + j);
           j = j - 1;
       }

       *(arr + (j + 1)) = key;
       i = i + 1;
   }
}

int main() {
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

  insertion_sort(array, COUNT);

  return 0;
}
