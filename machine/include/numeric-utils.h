#ifndef KERN_NUMERIC_UTILS
#define KERN_NUMERIC_UTILS

// IS_ALIGNED works by setting up a bitmask 
// (e.g. three bits padding -> 2^3 - 1 = 8 - 1 = 7 = 0b111)
// If (value AND bitmask) is zero, the value is aligned
#define IS_ALIGNED(value, pad) ((value & ((1 << pad) - 1)) == 0)

#define MIN(first, second) ((first) < (second) ? (first) : (second))
#define MAX(first, second) ((first) > (second) ? (first) : (second))

#define ROUND_UP(num, to) (((num) % (to)) > 0 ? (num) + ((to) - ((num) % (to))) : (num))

#endif /* KERN_NUMERIC_UTILS */
