int main(int argc, char** argv) {
  // test all characters of a hex integer literal
  if (0x123456789ABCDEF0 == 1311768467463790320)
    return 42;
  else
    return 0;
}