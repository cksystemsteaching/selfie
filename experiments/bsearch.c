/*
  Bsearch function searches the sorted array for an object that is equivalent to key.
  The array contains COUNT elements, each of size byte(s).
*/
uint64_t COUNT = 3000;
uint64_t STEP  = 2;
uint64_t* array;

uint64_t SIZEOFUINT64 = 8; // must be the same as REGISTERSIZE

uint64_t compare(uint64_t op1, uint64_t* op2) {
  if (op1 == *op2)
    return 0;
  else if (op1 < *op2)
    return 1;
  else
    return 2;
}

uint64_t bsearch(uint64_t key, uint64_t* base, uint64_t num, uint64_t size) {
	uint64_t* pivot;
	uint64_t  result;

  // base should be casted to (const char *) so that
  // pointer arithmetic adds one byte each time in (base + (num / 2) * size)
  // but we don't have char type so always size = 1.
	while (num != 0) {
		pivot = base + (num / 2) * size;
		result = compare(key, pivot);

		if (result == 0)
			return *pivot;

		if (result == 2) {
			base = pivot + size;
			num = num - 1;
		}
		num = num / 2;
	}

	return 0;
}

int main() {
  uint64_t    i;
  uint64_t    item;

  // array should be sorted
  array = malloc(COUNT * SIZEOFUINT64);
  i = 0;
  while (i < COUNT) {
    *(array + i) = i * STEP;
    i = i + 1;
  }

  //klee_assume(*element <= cnt*step);
  //klee_assume(*element >= 0);
  item = input(0, COUNT * STEP, 1);

  return bsearch(item, array, COUNT, 1);
}
