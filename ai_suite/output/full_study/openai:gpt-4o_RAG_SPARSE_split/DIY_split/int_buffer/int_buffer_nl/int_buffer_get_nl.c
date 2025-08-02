#include <stdlib.h>
#include <stdbool.h>

struct int_array {
    int values[10];
};

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
/*@ 
predicate int_array(struct int_array *arr, list<int> values) =
    arr->values |-> ?vs &*& length(vs) == 10 &*& ints(arr->values, 10, vs) &*& values == vs;
@*/

int get(struct int_array *arr, int index)
    //@ requires int_array(arr, ?values) &*& 0 <= index &*& index < 10;
    //@ ensures int_array(arr, values) &*& result == nth(index, values);
{
    //@ open int_array(arr, values);
    int result = arr->values[index];
    //@ close int_array(arr, values);
    return result;
}