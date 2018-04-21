void initLibrary();
void print(uint64_t* s);
void printInteger(uint64_t i);
void printString(uint64_t* s);
void println();
uint64_t main() {
  uint64_t* data;
  uint64_t i;
  initLibrary();
  data = malloc(39*8);
  *(data + 0) = (uint64_t) "void initLibrary();";
  *(data + 1) = (uint64_t) "void print(uint64_t* s);";
  *(data + 2) = (uint64_t) "void printInteger(uint64_t i);";
  *(data + 3) = (uint64_t) "void printString(uint64_t* s);";
  *(data + 4) = (uint64_t) "void println();";
  *(data + 5) = (uint64_t) "uint64_t main() {";
  *(data + 6) = (uint64_t) "  uint64_t* data;";
  *(data + 7) = (uint64_t) "  uint64_t i;";
  *(data + 8) = (uint64_t) "  initLibrary();";
  *(data + 9) = (uint64_t) "  data = malloc(39*8);";
  *(data + 10) = (uint64_t) "  i = 0;";
  *(data + 11) = (uint64_t) "  while (i < 10) {";
  *(data + 12) = (uint64_t) "    print(*(data + i));";
  *(data + 13) = (uint64_t) "    println();";
  *(data + 14) = (uint64_t) "    i = i + 1;";
  *(data + 15) = (uint64_t) "  }";
  *(data + 16) = (uint64_t) "  // data assignments with formatting";
  *(data + 17) = (uint64_t) "  i = 0;";
  *(data + 18) = (uint64_t) "  while (i < 39) {";
  *(data + 19) = (uint64_t) "    print(*(data + 36));";
  *(data + 20) = (uint64_t) "    printInteger(i);";
  *(data + 21) = (uint64_t) "    print(*(data + 37));";
  *(data + 22) = (uint64_t) "    printString(*(data + i));";
  *(data + 23) = (uint64_t) "    print(*(data + 38));";
  *(data + 24) = (uint64_t) "    println();";
  *(data + 25) = (uint64_t) "    i = i + 1;";
  *(data + 26) = (uint64_t) "  }";
  *(data + 27) = (uint64_t) "  // printing the while loops";
  *(data + 28) = (uint64_t) "  i = 10;";
  *(data + 29) = (uint64_t) "  while (i < 36) {";
  *(data + 30) = (uint64_t) "    print(*(data + i));";
  *(data + 31) = (uint64_t) "    println();";
  *(data + 32) = (uint64_t) "    i = i + 1;";
  *(data + 33) = (uint64_t) "  }";
  *(data + 34) = (uint64_t) "  return 0;";
  *(data + 35) = (uint64_t) "}";
  *(data + 36) = (uint64_t) "  *(data + ";
  *(data + 37) = (uint64_t) ") = (uint64_t) ";
  *(data + 38) = (uint64_t) ";";
  i = 0;
  while (i < 10) {
    print(*(data + i));
    println();
    i = i + 1;
  }
  // data assignments with formatting
  i = 0;
  while (i < 39) {
    print(*(data + 36));
    printInteger(i);
    print(*(data + 37));
    printString(*(data + i));
    print(*(data + 38));
    println();
    i = i + 1;
  }
  // printing the while loops
  i = 10;
  while (i < 36) {
    print(*(data + i));
    println();
    i = i + 1;
  }
  return 0;
}
