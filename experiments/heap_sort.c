/*
  This file is a C* translation of the original implementation
  done by Alireza Abyaneh.
*/

uint64_t* malloc(uint64_t size);

void swap(uint64_t* op1, uint64_t* op2) {
  uint64_t temp;

  temp = *op1;
  *op1 = *op2;
  *op2 = temp;
}

void heapify(uint64_t* arr, uint64_t n, uint64_t i) {
  uint64_t largest;
  uint64_t l;
  uint64_t r;

  largest = i; // Initialize largest as root
  l = 2*i + 1; // left = 2*i + 1
  r = 2*i + 2; // right = 2*i + 2

  // If left child is larger than root
  if (l < n)
    if (*(arr + l) > *(arr + largest))
      largest = l;

  // If right child is larger than largest so far
  if (r < n)
    if (*(arr + r) > *(arr + largest))
      largest = r;

  // If largest is not root
  if (largest != i) {
    swap((arr + i), (arr + largest));

    // Recursively heapify the affected sub-tree
    heapify(arr, n, largest);
  }
}

// main function to do heap sort
void heapSort(uint64_t* arr, uint64_t n) {
  uint64_t i;

  // Build heap (rearrange array)
  i = n / 2;
  while (i > 0) {
    heapify(arr, n, i - 1);

    i = i - 1;
  }

  // One by one extract an element from heap
  i = n;
  while (i > 0) {
    // Move current root to end
    swap(arr, (arr + (i-1)));

    // call max heapify on the reduced heap
    heapify(arr, i-1, 0);

    i = i - 1;
  }
}

uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t v1;
  uint64_t cnt;
  uint64_t* arr;

  cnt = 300;
  arr = malloc(cnt * 8);

  v1 = 0;
  while (v1 < cnt) {
    if (v1 != cnt/2)
      *(arr + v1) = cnt - v1;
    v1 = v1 + 1;
  }

  *(arr + cnt/2) = input(0, 2*cnt-1, 1);

  heapSort(arr, cnt);

  return 0;
}