int main(int argc, char** argv) {
  uint64_t integer;

  integer = 1;

  integer = !integer;

  if (!integer)
    if (!(!integer))
      return 0;
    else
      return 42 * !integer;
  else
    return 0;
}