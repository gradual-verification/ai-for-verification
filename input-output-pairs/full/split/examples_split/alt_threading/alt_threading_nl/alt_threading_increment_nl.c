#include "stdlib.h"

struct thread;


// TODO: make this function pass the verification
/**
 * Description:
 * The `increment` function increments the value stored at the memory location pointed to by `cell`.
 *
 * @param cell - A pointer to an integer.
 *
 * The function retrieves the integer value at `cell`, increments it by 1, and stores the result back
 * in the same memory location.
 */
void increment(int *cell)
{
    (*cell)++;
}

