uint64_t* dot;

uint64_t* strchr(uint64_t* s, uint64_t c) {
  while (1) {
    if (*s == c)
      return s;
    if (*s == 0)
      return (uint64_t*) 0;

    s = s + 1;
  }
}

uint64_t* strrchr(uint64_t* s, uint64_t c) {
  uint64_t* found;
  uint64_t* p;

  if (c == 0)
    return strchr(s, 0);

  found = (uint64_t*) 0;
  p = strchr(s, c);
  while (p != (uint64_t*) 0) {
    found = p;
    s = p + 1;
    p = strchr(s, c);
  }

  return found;
}

uint64_t* dirname(uint64_t* path) {
  uint64_t* last_slash;
  uint64_t* runp;
  uint64_t  loop;

  dot = (uint64_t*) ".";

  if (path != (uint64_t*) 0)
    last_slash = strrchr(path, '/');
  else
    last_slash = (uint64_t*) 0;

  if (last_slash != (uint64_t*) 0) {
    if (last_slash != path) {
      if (*(last_slash + 1) == 0) {

        runp = last_slash;
        loop = 1;
        while (loop) {
          if (runp != path) {
            if (*(runp - 1) != '/')
              loop = 0;
            else
              runp = runp - 1;
          } else
            loop = 0;
        }

        loop = 1;
        while (loop) {
          if (runp != path) {
            runp = runp - 1;
            if (*runp == '/') {
              last_slash = runp;
              loop = 0;
            }
          } else {
            last_slash = (uint64_t*) 0;
            loop = 0;
          }
        }
      }
    }
  }

  if (last_slash != (uint64_t*) 0) {
    runp = last_slash;
    loop = 1;
    while (loop) {
      if (runp != path) {
        if (*(runp - 1) != '/')
          loop = 0;
        else
          runp = runp - 1;
      } else
        loop = 0;
    }

    if (runp == path) {
      if (last_slash == path + 1)
  	    last_slash = last_slash + 1;
  	  else
  	    last_slash = path + 1;
    } else
      last_slash = runp;

    *last_slash = 0;

  } else
    path = dot;

  return path;
}

uint64_t main() {
  uint64_t* str;
  uint64_t* ptr;
  uint64_t  cnt;
  uint64_t  i;

  cnt = 17;
  str = malloc(cnt * 8);
  i = 0;
  while (i < cnt-1) {
    *(str + i) = input(0, 125, 1);
    i = i + 1;
  }
  *(str + cnt - 1) = 0;

  ptr = dirname(str);

  return 0;
}
