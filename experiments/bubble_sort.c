uint64_t COUNT = 100;
uint64_t* array;

uint64_t SIZEOFUINT64 = 8; // must be the same as REGISTERSIZE

void swap(uint64_t* xp, uint64_t* yp) {
  uint64_t temp;

  temp  = *(xp);
  *(xp) = *(yp);
  *(yp) = temp;
}

void bubble_sort(uint64_t* arr, uint64_t n) {
   uint64_t i;
   uint64_t j;
   uint64_t swapped;

   i = 0;
   while (i < n - 1) {
     swapped = 0;
     j = 0;

     while (j < n - i - 1) {
       if (*(arr + j) > *(arr + (j + 1))) {
         swap(arr + j, arr + (j + 1));
         swapped = 1;
       }
       j = j + 1;
     }

     i = i + 1;
     if (swapped == 0)
      return;
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
  bubble_sort(array, COUNT);

  return 0;
}
