/*
  This file is a C* implementation of word count
  written by Alireza Abyaneh.
*/

uint64_t CHAR_EOF          =  -1;
uint64_t CHAR_TAB          =   9;
uint64_t CHAR_LF           =  10;
uint64_t CHAR_CR           =  13;
uint64_t CHAR_SPACE        = ' ';

uint64_t  line_number = 0;
uint64_t  word_number = 0;
uint64_t  byte_number = 0;

uint64_t is_character_new_line(uint64_t c) {
  if (c == CHAR_LF)
    return 1;
  else if (c == CHAR_CR)
    return 1;
  else
    return 0;
}

uint64_t is_character_whitespace(uint64_t c) {
  if (c == CHAR_SPACE)
    return 1;
  else if (c == CHAR_TAB)
    return 1;
  else
    return is_character_new_line(c);
}

void wc(uint64_t* s) {
  while (*s != CHAR_EOF) {
    while (is_character_whitespace(*s)) {
      if (*s == CHAR_LF) {
        line_number = line_number + 1;
      }
      byte_number = byte_number + 1;
      s = s + 1;
    }

    if (*s != CHAR_EOF) {
      word_number = word_number + 1;
      byte_number = byte_number + 1;

      s = s + 1;

      while (is_character_whitespace(*s) == 0) {
        if (*s == CHAR_EOF)
          return;

        byte_number = byte_number + 1;

        s = s + 1;
      }
    }

  }
}

uint64_t main() {
  uint64_t* str;
  uint64_t  cnt;
  uint64_t  i;

  cnt = 9;
  str = malloc(cnt * 8);
  i = 0;
  while (i < cnt-1) {
    *(str + i) = input(5, 125, 1);
    i = i + 1;
  }
  *(str + cnt-1) = -1;

  wc(str);

  return 0;
}