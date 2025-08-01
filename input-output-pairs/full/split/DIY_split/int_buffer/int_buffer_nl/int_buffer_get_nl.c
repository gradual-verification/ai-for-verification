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
int get(struct int_array *arr, int index)
{
    return arr->values[index];
}
