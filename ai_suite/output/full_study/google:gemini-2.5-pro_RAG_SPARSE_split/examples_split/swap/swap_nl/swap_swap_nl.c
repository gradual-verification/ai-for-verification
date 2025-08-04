#include "stdlib.h"

struct point {
    int x;
    int y;
};



// TODO: make this function pass the verification
/*** 
 * Description:
The swap function takes two integer pointers as parameters and swaps the values they point to.

@param a - Pointer to the first integer value to be swapped.
@param b - Pointer to the second integer value to be swapped.

It makes sure that the values pointed to by a and b are swapped correctly.
*/
/*@
requires integer(a, ?val_a) &*& integer(b, ?val_b);
ensures integer(a, val_b) &*& integer(b, val_a);
@*/
void swap(int *a, int *b)
{
    int tmp = *a;
    *a = *b;
    *b = tmp;
}