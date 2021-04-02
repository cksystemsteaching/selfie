#include "tinycstd.h"

#include "console.h"
#include "diag.h"
#include "syscalls.h"
#include "compiler-utils.h"
#include <stdarg.h>

// Format string handling
typedef ssize_t (*put_handler)(const char* buffer, ssize_t len, void** context);
int handle_format_string(const char* format, va_list args, put_handler handler, void* context);

// Function required by libgcc for a freestanding environment

void* memmove(void* dest, const void* source, size_t num) {
  uint8_t* dst = (uint8_t*) dest;
  uint8_t* src = (uint8_t*) source;

  while (num > 0) {
    *(dst++) = *(src++);
    num--;
  }

  return dest;
}

void* memcpy (void* destination, const void* source, size_t num) {
  return memmove(destination, source, num);
}

void* memset(void* ptr, int value, size_t num) {
  uint8_t* char_ptr = (uint8_t*) ptr;

  while (num > 0) {
    *char_ptr = (uint8_t) value;

    char_ptr++;
    num--;
  }

  return ptr;
}

int memcmp(const void* ptr1, const void* ptr2, size_t num) {
  uint8_t* p1 = (uint8_t*) ptr1;
  uint8_t* p2 = (uint8_t*) ptr2;

  for (size_t i = 0; i < num; i++) {
    if (p1[i] < p2[i])
      return -1;
    if (p1[i] > p2[i])
      return 1;
  }

  return 0;
}

uint64_t strlen(const char* str) {
  uint64_t len = 0;

  while (str && *(str++))
    ++len;

  return len;
}

ssize_t strncmp(const char* first, const char* second, size_t n) {
  for (size_t i = 0; i < n; i++) {
    if (first[i] < second[i])
      return -1;
    else if(first[i] > second[i])
      return 1;
    else if (first[i] == '\0') // implies second[i] == '\0'
      break;
  }
  return 0;
}

const char* strchr(const char* str, int c) {
  while (*str != '\0') {
    if (*str == ((char) c))
      return str;
    str++;
  }

  if (c == '\0')
    return str;
  else
    return NULL;
}

size_t strlcpy(char* dest, const char* src, size_t n) {
  size_t copied = 0;

  while (copied < (n - 1)) {
    if (src[copied] == '\0')
      break;

    dest[copied] = src[copied];
    copied++;
  }
  dest[copied] = '\0';

  return copied;
}

char* itoa_ext(uintmax_t value, uint8_t base, uint8_t bits, bool sign);
int printf(const char* format, ...) {
  va_list args;
  va_start(args, format);

  int result = va_printf(format, args);

  va_end(args);

  return result;
}

ssize_t sprintf_put(const char* str, ssize_t len, void** ctxt) {
  strlcpy((*ctxt)+1, str, len+1); // len+1 due to \0
  return len;
}
int sprintf(char* buf, const char* format, ...) {
  va_list args;
  va_start(args, format);

  int ret = handle_format_string(format, args, sprintf_put, buf);
  // No need for explicitly setting \0 at the end - strlcpy in sprintf_put already does the job

  va_end(args);

  return ret;
}

void puts(const char* s) {
  console_puts(s, strlen(s));
}

void putc(char c) {
  console_putc(c);
}

int dprintf(int fd, const char* format, ...) {
  va_list args;
  va_start(args, format);
  int ret;

  if (fd_is_stdio(fd))
    ret = va_printf(format, args);
  else
    panic("dprintf called with non-stdio descriptor (no write support on files)");

  va_end(args);

  return ret;
}

ssize_t printf_puts(const char* str, ssize_t len, void** ctxt) {
  UNUSED_VAR(ctxt);
  return console_puts(str, len);
}

int va_printf(const char* format, va_list args) {
  return handle_format_string(format, args, printf_puts, NULL);
}

// TODO: This function mingles signed and unsigned characters of various sizes (32bit and 64bit).
//       As long as the format operation does not exceed 2147483647 characters
//       (2^31 - 1 due to the sign bit), it should work.
//       However, this is still unclean and must be handled correctly
int handle_format_string(const char* format, va_list args, put_handler handler, void* context) {
  int written = 0;
  size_t len;
  ssize_t handled;
  const char* fmt_pos;

  while (1) {
    fmt_pos = strchr(format, '%');

    if (fmt_pos == NULL) {
      // Found no format specifier - print rest and return
      len = strlen(format);
      handled = handler(format, len, &context);
      return written + handled;
    } else {
      // Found format specifier - print everything before it and handle specifier
      handled = handler(format, fmt_pos - format, &context);
      written += handled;
      format = fmt_pos + 1;
      switch (*format) {
        case '%':
          handled = handler("%", 1, &context);
          written += handled;
          format++;
          break;
        case 'c': {
          char c = va_arg(args, int); // char is "promoted" to int by variable args
          handled = handler(&c, 1, &context);
          written += handled;
          format++;
          break;
        }
        case 'd':
        case 'i': {
          int i = va_arg(args, int);
          char* buf = itoa_ext(i, 10, sizeof(int) * 8, true);
          len = strlen(buf);
          handled = handler(buf, len, &context);
          written += handled;
          format++;
          break;
        }
        case 'u': {
          uintmax_t i = va_arg(args, uintmax_t);
          char* buf = itoa_ext(i, 10, sizeof(uintmax_t) * 8, false);
          len = strlen(buf);
          handled = handler(buf, len, &context);
          written += handled;
          format++;
          break;
        }
        case 'x':
        case 'X': {
          uintmax_t i = va_arg(args, uintmax_t);
          char* buf = itoa_ext(i, 16, sizeof(uintmax_t) * 8, false);
          len = strlen(buf);
          handled = handler(buf, len, &context);
          written += handled;
          format++;
          break;
        }
        case 'p': {
          void* i = va_arg(args, void*);
          char* buf = itoa_ext((uintmax_t)i, 16, sizeof(void*) * 8, false);
          // Fill missing bytes with zeros
          // One hex number is a nibble (4 bits) -> two represent one byte
          size_t filldiff = (sizeof(void*) * 2) - strlen(buf);
          while (filldiff != 0) {
            handled = handler("0", 1, &context);
            written += handled;
            filldiff--;
          }

          len = strlen(buf);
          handled = handler(buf, len, &context);
          written += handled;
          format++;
          break;
        }
        case 's': {
          const char* s = va_arg(args, const char*);
          len = strlen(s);
          handled = handler(s, len, &context);
          written += handled;
          format++;
          break;
        }
        default:
          handled = handler("%", 1, &context);
          handled += handler(format, 1, &context);
          written += handled;
          format++;
          break;
      }
    }
  }
}


// TODO: Not thread-safe
char* itoa_ext(uintmax_t value, uint8_t base, uint8_t bits, bool sign) {
  const char* conv = "0123456789ABCDEF";
  static char buf[2 + sizeof(uintmax_t) * 8]; // maximum integer bits + minus sign + null

  char* pos = buf + sizeof(buf) - 1;
  bool negative = false;

  // If sign bit is set, convert to positive number (two's complement)
  if (sign && (value & (1 << (bits - 1)))) {
    negative = true;

    value = ~value + 1;
    if (bits < sizeof(uintmax_t) * 8)
      // Cut off irrelevant bits
      value = value & ((1ULL << bits) - 1);
  }

  *pos = '\0';

  if (value != 0)
    while (value != 0) {
      uint8_t rem = value % base;

      pos--;
      *pos = conv[rem];

      value = value / base;
    }
  else {
    pos--;
    *pos = conv[0];
  }

  if (negative) {
    pos--;
    *pos = '-';
  }

  return pos;
}
