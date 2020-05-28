/**
 * @brief Small recursive function to print out a number in hexadecimal
 *
 * While debugging problems while setting up the global pointer, it was not possible to use
 * a fully-fledged itoa implementation because memory regions that require the gp to function
 * (BSS, data) were not an option.
 * This function is called recursively and prints the current hexadecimal digit in post-order.
 *
 * @param val The value to print
 * @param pos The current character count
 * @param maxLen The maximum amount of characters to print
 */
void print_hex_internal(uint64_t val, uint64_t pos, uint64_t maxLen) {
    if (pos >= maxLen)
        return;

    uint64_t rest = val % 16;
    val = val / 16;

    print_hex_internal(val, pos+1, maxLen);
    if (rest >= 0 && rest < 10) {
        sbi_ecall_console_putc('0'+rest);
    } else {
        sbi_ecall_console_putc('A'+(rest-10));
    }
}

void print_hex(uint64_t val) {
    sbi_ecall_console_putc('0');
    sbi_ecall_console_putc('x');

    print_hex_internal(val, 0, 8);
}
