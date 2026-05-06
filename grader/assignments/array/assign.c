int main(int argc, char** argv) {
  uint64_t* arr;

  arr = malloc(sizeof(uint64_t) * 4);

  arr[0] = 4;
  arr[1] = 8;
  arr[2]= 14;
  arr[3] = 16;

  return *arr + *(arr + 1) + *(arr + 2) + *(arr + 3);
}
