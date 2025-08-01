#include <stdlib.h>
#include <stdbool.h>

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
{
    arr->values[index] = value;
}
