#include <stdlib.h>
#include <stdbool.h>

struct int_array {
    int values[10];
};

/*@
// Define a predicate for the int_array structure
predicate int_array(struct int_array *arr; list<int> vs) =
    arr->values[0..10] |-> vs &*& length(vs) == 10;
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
/*@
requires int_array(arr, ?vs) &*& 0 <= index &*& index < 10;
ensures int_array(arr, vs) &*& result == nth(index, vs);
@*/
int get(struct int_array *arr, int index)
{
    return arr->values[index];
}