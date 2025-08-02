#include "stdlib.h"
#include "stdio.h"
//@ #include "arrays.gh"
//@ #include "quantifiers.gh"
//@ #include "target.gh"

// TODO: make this function pass the verification
/***
 * Description:
The read_int function reads a single integer from standard input.

@return The integer value read.

It requires and ensures nothing.
*/
int read_int()
//@ requires true;
//@ ensures true;
{
    int x;
    int result = scanf("%i", &x);
    if (result < 1) abort();
    return x;
}