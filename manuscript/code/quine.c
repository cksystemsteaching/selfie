void initLibrary();uint64_t* zalloc(uint64_t s);
void print(uint64_t* s);void println();
void printInteger(uint64_t i);void printString(uint64_t* s);
uint64_t main(){
  uint64_t* data;
  uint64_t i; i = 0;
  data = zalloc(33*8);
  initLibrary();
  *(data + 0) = (uint64_t) "void initLibrary();uint64_t* zalloc(uint64_t s);";
  *(data + 1) = (uint64_t) "void print(uint64_t* s);void println();";
  *(data + 2) = (uint64_t) "void printInteger(uint64_t i);void printString(uint64_t* s);";
  *(data + 3) = (uint64_t) "uint64_t main(){";
  *(data + 4) = (uint64_t) "  uint64_t* data;";
  *(data + 5) = (uint64_t) "  uint64_t i; i = 0;";
  *(data + 6) = (uint64_t) "  data = zalloc(33*8);";
  *(data + 7) = (uint64_t) "  initLibrary();";
  *(data + 8) = (uint64_t) "  while(i < 8){";
  *(data + 9) = (uint64_t) "    print(*(data + i));println();";
  *(data + 10) = (uint64_t) "    i = i + 1;";
  *(data + 11) = (uint64_t) "  }";
  *(data + 12) = (uint64_t) "  // data assignments with formatting";
  *(data + 13) = (uint64_t) "  i = 0;";
  *(data + 14) = (uint64_t) "  while(i < 33){";
  *(data + 15) = (uint64_t) "    print(*(data + 30));";
  *(data + 16) = (uint64_t) "    printInteger(i);";
  *(data + 17) = (uint64_t) "    print(*(data + 31));";
  *(data + 18) = (uint64_t) "    printString(*(data + i));";
  *(data + 19) = (uint64_t) "    print(*(data + 32));println();";
  *(data + 20) = (uint64_t) "    i = i + 1;";
  *(data + 21) = (uint64_t) "  }";
  *(data + 22) = (uint64_t) "  // printing the while loops";
  *(data + 23) = (uint64_t) "  i = 8;";
  *(data + 24) = (uint64_t) "  while(i < 30){";
  *(data + 25) = (uint64_t) "    print(*(data + i));println();";
  *(data + 26) = (uint64_t) "    i = i + 1;";
  *(data + 27) = (uint64_t) "  }";
  *(data + 28) = (uint64_t) "  return 0;";
  *(data + 29) = (uint64_t) "}";
  *(data + 30) = (uint64_t) "  *(data + ";
  *(data + 31) = (uint64_t) ") = (uint64_t) ";
  *(data + 32) = (uint64_t) ";";
  while(i < 8){
    print(*(data + i));println();
    i = i + 1;
  }
  // data assignments with formatting
  i = 0;
  while(i < 33){
    print(*(data + 30));
    printInteger(i);
    print(*(data + 31));
    printString(*(data + i));
    print(*(data + 32));println();
    i = i + 1;
  }
  // printing the while loops
  i = 8;
  while(i < 30){
    print(*(data + i));println();
    i = i + 1;
  }
  return 0;
}
