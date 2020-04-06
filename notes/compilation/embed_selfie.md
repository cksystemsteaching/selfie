# Embed Selfie as a char array

1. Start (neo)vim and
2. Load the file inside using `:r !xxd <file.c>`
3. Remove the leading offset using a visual block
4. Remove the trailing ASCII representation. Beware the last line (might not be filled)
5. Split into single bytes: `:%s/\(\w\w\)\(\w\w\)/\1 \2/g`
6. Add colon and 0x prefix: `:%s/\(\w\w\)/0x}1,/g`


# Easier variation
`xxd -i <file.c>`
