// This C* code outputs its own source code: quine.c in C*
void initLibrary();
void print(uint64_t* s);
void printInteger(uint64_t i);
void printString(uint64_t* s);
void println();
uint64_t main() {
  uint64_t* data;
  uint64_t i;
  initLibrary();
  data = malloc(41*8);
  *(data + 0) = (uint64_t) "// This C* code outputs its own source code: quine.c in C*";
  *(data + 1) = (uint64_t) "void initLibrary();";
  *(data + 2) = (uint64_t) "void print(uint64_t* s);";
  *(data + 3) = (uint64_t) "void printInteger(uint64_t i);";
  *(data + 4) = (uint64_t) "void printString(uint64_t* s);";
  *(data + 5) = (uint64_t) "void println();";
  *(data + 6) = (uint64_t) "uint64_t main() {";
  *(data + 7) = (uint64_t) "  uint64_t* data;";
  *(data + 8) = (uint64_t) "  uint64_t i;";
  *(data + 9) = (uint64_t) "  initLibrary();";
  *(data + 10) = (uint64_t) "  data = malloc(41*8);";
  *(data + 11) = (uint64_t) "  // printing source code before stored code";
  *(data + 12) = (uint64_t) "  i = 0;";
  *(data + 13) = (uint64_t) "  while (i < 11) {";
  *(data + 14) = (uint64_t) "    print(*(data + i));";
  *(data + 15) = (uint64_t) "    println();";
  *(data + 16) = (uint64_t) "    i = i + 1;";
  *(data + 17) = (uint64_t) "  }";
  *(data + 18) = (uint64_t) "  // printing stored source code";
  *(data + 19) = (uint64_t) "  i = 0;";
  *(data + 20) = (uint64_t) "  while (i < 41) {";
  *(data + 21) = (uint64_t) "    print(*(data + 38));";
  *(data + 22) = (uint64_t) "    printInteger(i);";
  *(data + 23) = (uint64_t) "    print(*(data + 39));";
  *(data + 24) = (uint64_t) "    printString(*(data + i));";
  *(data + 25) = (uint64_t) "    print(*(data + 40));";
  *(data + 26) = (uint64_t) "    println();";
  *(data + 27) = (uint64_t) "    i = i + 1;";
  *(data + 28) = (uint64_t) "  }";
  *(data + 29) = (uint64_t) "  // printing source code after stored code";
  *(data + 30) = (uint64_t) "  i = 11;";
  *(data + 31) = (uint64_t) "  while (i < 38) {";
  *(data + 32) = (uint64_t) "    print(*(data + i));";
  *(data + 33) = (uint64_t) "    println();";
  *(data + 34) = (uint64_t) "    i = i + 1;";
  *(data + 35) = (uint64_t) "  }";
  *(data + 36) = (uint64_t) "  return 0;";
  *(data + 37) = (uint64_t) "}";
  *(data + 38) = (uint64_t) "  *(data + ";
  *(data + 39) = (uint64_t) ") = (uint64_t) ";
  *(data + 40) = (uint64_t) ";";
  // printing source code before stored code
  i = 0;
  while (i < 11) {
    print(*(data + i));
    println();
    i = i + 1;
  }
  // printing stored source code
  i = 0;
  while (i < 41) {
    print(*(data + 38));
    printInteger(i);
    print(*(data + 39));
    printString(*(data + i));
    print(*(data + 40));
    println();
    i = i + 1;
  }
  // printing source code after stored code
  i = 11;
  while (i < 38) {
    print(*(data + i));
    println();
    i = i + 1;
  }
  return 0;
}
