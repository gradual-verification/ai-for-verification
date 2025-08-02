#include <stdio.h>


// TODO: make this function pass the verification
/***
 * Description:
 * The `to_verify` function increments the fourth element (`arr[3]`) of a 
 * predefined array {0, 10, 20, 30, 40, 50, 60, 70, 80, 90} and returns its previous value.
 *
 * @param arr - A pointer to an array of at least 10 integers.
 * 
 * It makes sure that the return value is the original value of `arr[3]` before incrementing (i.e., 30),
 * and arr is modified to {0, 10, 20, 31, 40, 50, 60, 70, 80, 90}.
 */
/*@
  requires ints(arr, 10, ?values) &*& length(values) == 10 &*& nth(3, values) == 30;
  ensures ints(arr, 10, update(3, 31, values)) &*& result == 30;
@*/
int to_verify(int* arr)
{
    return arr[3]++;
}