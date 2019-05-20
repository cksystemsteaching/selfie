uint64_t COUNT = 3000;
uint64_t STEP  = 2;
uint64_t* array;

uint64_t SIZEOFUINT64 = 8;

uint64_t compare(uint64_t op1, uint64_t* op2) {
  return (op1 == *op2);
}

uint64_t lfind_(uint64_t key, uint64_t* base, uint64_t* nmemb, uint64_t size) {
  uint64_t* result;
  uint64_t  cnt;
  uint64_t  loop;

  result = base;
  cnt    = 0;

  // base should be casted to (const char *) or (const void *) so that
  // pointer arithmetic adds one byte each time in (result + size)
  // but we don't have char type so always size = 1.
  loop = 1;
  while (loop) {
    if (cnt < *nmemb) {
      if (compare(key, result) == 0) {
        result = result + size;
        cnt    = cnt + 1;
      } else
        loop = 0;
    } else
      loop = 0;
  }

  if (cnt < *nmemb)
    return *result;
  else
    return 0;
}

int main() {
  uint64_t    i;
  uint64_t    item;
  uint64_t* length;

  // array should be sorted
  array = malloc(COUNT * SIZEOFUINT64);
  i = 0;
  while (i < COUNT) {
    *(array + i) = 2 * COUNT - i * STEP;
    i = i + 1;
  }

  //klee_assume(*element <= (cnt+1)*step);
  //klee_assume(*element >= 0);
  item = input(0, (COUNT+1) * STEP, 1);

  length   = malloc(1 * SIZEOFUINT64);
  *length  = COUNT;

  return lfind_(item, array, length, 1);
}
