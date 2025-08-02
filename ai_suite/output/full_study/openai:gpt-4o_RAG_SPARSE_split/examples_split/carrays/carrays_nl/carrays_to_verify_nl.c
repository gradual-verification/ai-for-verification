#include <stdio.h>

//@ #include "prelude.h"

/*@
predicate array_of_integers(int *arr, int count, list<int> values) =
    count == 0 ?
        values == nil
    :
        integer(arr, ?v) &*& array_of_integers(arr + 1, count - 1, ?vs) &*& values == cons(v, vs);
@*/

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
requires array_of_integers(arr, 10, ?values) &*& length(values) >= 10 &*& nth(3, values) == 30;
ensures array_of_integers(arr, 10, update(3, 31, values)) &*& result == 30;
@*/
int to_verify(int* arr)
{
    return arr[3]++;
}