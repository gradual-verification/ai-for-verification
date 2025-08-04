#include <stdlib.h>
#include <stdbool.h>

/*@
#include "list.gh"

predicate int_array(struct int_array *arr; list<int> vs) =
    ints(arr->values, 10, vs) &*&
    malloc_block_int_array(arr);

@*/

struct int_array {
    int values[10];
};

// TODO: make this function pass the verification
/***
 * Description:
 * The `set` function sets the element at the given index in an int_array to be the given value.
 * 
 * @param arr: the int_array to be set
 * @param index: the index to be set into, which is >= 0 and < 10
 * @param value: the value to be set with
 * 
 * It makes sure that the new int_array is updated with the value. 
 */
void set(struct int_array *arr, int index, int value)
    //@ requires int_array(arr, ?old_vs) &*& 0 <= index &*& index < 10;
    //@ ensures int_array(arr, update(index, value, old_vs));
{
    arr->values[index] = value;
}