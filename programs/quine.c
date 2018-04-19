void initLibrary();uint64_t* zalloc(uint64_t s);
void print(uint64_t* s);void putCharacter(uint64_t* c);
void printInteger(uint64_t i);void printString(uint64_t* s);
uint64_t main(){
  uint64_t* data;
  uint64_t i; i = 0;
  data = zalloc(34*8);
  initLibrary();
  *(data + 0) = (uint64_t) "void initLibrary();uint64_t* zalloc(uint64_t s);";
  *(data + 1) = (uint64_t) "void print(uint64_t* s);void putCharacter(uint64_t* c);";
  *(data + 2) = (uint64_t) "void printInteger(uint64_t i);void printString(uint64_t* s);";
  *(data + 3) = (uint64_t) "uint64_t main(){";
  *(data + 4) = (uint64_t) "  uint64_t* data;";
  *(data + 5) = (uint64_t) "  uint64_t i; i = 0;";
  *(data + 6) = (uint64_t) "  data = zalloc(34*8);";
  *(data + 7) = (uint64_t) "  initLibrary();";
  *(data + 8) = (uint64_t) "  while(i < 8){";
  *(data + 9) = (uint64_t) "    print(*(data + i));";
  *(data + 10) = (uint64_t) "    putCharacter(10);";
  *(data + 11) = (uint64_t) "    i = i + 1;";
  *(data + 12) = (uint64_t) "  }";
  *(data + 13) = (uint64_t) "  // data assignments with formatting";
  *(data + 14) = (uint64_t) "  i = 0;";
  *(data + 15) = (uint64_t) "  while(i < 34){";
  *(data + 16) = (uint64_t) "    print(*(data + 32));";
  *(data + 17) = (uint64_t) "    printInteger(i);";
  *(data + 18) = (uint64_t) "    print(*(data + 33));";
  *(data + 19) = (uint64_t) "    printString(*(data + i));";
  *(data + 20) = (uint64_t) "    putCharacter(59);putCharacter(10);";
  *(data + 21) = (uint64_t) "    i = i + 1;";
  *(data + 22) = (uint64_t) "  }";
  *(data + 23) = (uint64_t) "  // printing the while loops";
  *(data + 24) = (uint64_t) "  i = 8;";
  *(data + 25) = (uint64_t) "  while(i < 32){";
  *(data + 26) = (uint64_t) "    print(*(data + i));";
  *(data + 27) = (uint64_t) "    putCharacter(10);";
  *(data + 28) = (uint64_t) "    i = i + 1;";
  *(data + 29) = (uint64_t) "  }";
  *(data + 30) = (uint64_t) "  return 0;";
  *(data + 31) = (uint64_t) "}";
  *(data + 32) = (uint64_t) "  *(data + ";
  *(data + 33) = (uint64_t) ") = (uint64_t) ";
  while(i < 8){
    print(*(data + i));
    putCharacter(10);
    i = i + 1;
  }
  // data assignments with formatting
  i = 0;
  while(i < 34){
    print(*(data + 32));
    printInteger(i);
    print(*(data + 33));
    printString(*(data + i));
    putCharacter(59);putCharacter(10);
    i = i + 1;
  }
  // printing the while loops
  i = 8;
  while(i < 32){
    print(*(data + i));
    putCharacter(10);
    i = i + 1;
  }
  return 0;
}
