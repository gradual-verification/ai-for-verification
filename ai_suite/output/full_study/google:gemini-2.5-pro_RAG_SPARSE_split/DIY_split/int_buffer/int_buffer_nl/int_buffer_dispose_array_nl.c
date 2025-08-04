#include <stdlib.h>
#include <stdbool.h>

struct int_array {
    int values[10];
};

/*@
predicate int_array(struct int_array *arr, list<int> vs) =
    malloc_block_int_array(arr) &*&
    ints(arr->values, 10, vs);
@*/

/***
 * Description:
 * The `dispose_array` function disposes an int_array.
 *
 * @param arr: the given int_array that has the property of int_array
 *
 * The function makes sure that the int_array is freed. 
 */
void dispose_array(struct int_array *arr)
    //@ requires int_array(arr, ?vs);
    //@ ensures emp;
{
    free(arr);
}