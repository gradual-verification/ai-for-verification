#include <stdlib.h>
#include <stdbool.h>

struct int_array {
    int values[10];
};

// TODO: make this function pass the verification
/***
 * Description:
 * The `dispose_array` function disposes an int_array.
 *
 * @param arr: the given int_array that has the property of int_array
 *
 * The function makes sure that the int_array is freed. 
 */
//@ predicate int_array(struct int_array *arr) = malloc_block_ints(arr->values, 10) &*& ints(arr->values, 10, _);

void dispose_array(struct int_array *arr)
    //@ requires int_array(arr);
    //@ ensures emp;
{
    //@ open int_array(arr);
    free(arr);
}