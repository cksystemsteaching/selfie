# Stack
## make targets
* all make targets (except `min`) only use the hi page `0xFFFFF`
    * `min` sets lowest hi page from `0xFFFFF` to `0x49`

## misc. tests
Compiling the program (`./selfie -c selfie.c -m 128 -c test.c`)
```
uint64_t main() {
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
while (1)
    return 0;
}
```
(which contains 36 `while (1)`) takes only one page on the stack. If one more `while (1)` is added, the lowest hi page will be set from `0xFFFFF` to `0xFFFFE`.
