#include <stdio.h>


// TODO: make this function pass the verification
/***
 * Description:
 * The `array_test1` function reads three consecutive integer values from an array.
 *
 * @param a - A pointer to an array containing at least 3 elements.
 *
 * The function makes sure that the array is not changed.
 */
/*@
requires [?f]ints(a, ?n, ?values) &*& n >= 3;
ensures [f]ints(a, n, values);
@*/
void array_test1(int* a)
{
    int tmp0 = a[0];
    int tmp1 = a[1];
    int tmp2 = a[2];
}