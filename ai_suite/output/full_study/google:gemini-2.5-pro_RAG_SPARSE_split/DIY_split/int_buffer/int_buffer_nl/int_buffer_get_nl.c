#include <stdlib.h>
#include <stdbool.h>

struct int_array {
    int values[10];
};

/*@
// Predicate representing an int_array struct and its contents.
predicate int_array_p(struct int_array *arr; list<int> vs) =
    // The 'values' field is an array of 10 integers, represented by the list 'vs'.
    ints(arr->values, 10, vs) &*&
    // The memory block for the struct itself is allocated.
    malloc_block_int_array(arr);
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `get` function gets the element at the given index in an int_array.
 * 
 * @param arr: the int_array.
 * @param index: the index to be accessed, which is >= 0 and < 10
 * 
 * It makes sure that the int_array is not changed and it returns the element at index in arr. 
 */
int get(struct int_array *arr, int index)
    //@ requires int_array_p(arr, ?values) &*& 0 <= index &*& index < 10;
    //@ ensures int_array_p(arr, values) &*& result == nth(index, values);
{
    // The array access arr->values[index] is verified because:
    // 1. The precondition provides the `ints(arr->values, 10, values)` chunk via `int_array_p`.
    // 2. The precondition asserts that `0 <= index < 10`, which is the valid range for the array.
    // VeriFast knows that the value of this expression is `nth(index, values)`.
    // The `int_array_p` chunk is preserved since this is a read-only operation.
    return arr->values[index];
}