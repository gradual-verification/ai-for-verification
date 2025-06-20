#include <stdlib.h>
#include <stdbool.h>

struct int_array {
    int values[10];
};

// TODO: make this function pass the verification
/***
 * Description:
 * The `create_array` function creates an int_array with its values as 10 zeros.
 *
 * It makes sure that the new int_array has 10 zeros in its value. 
 */
struct int_array *create_array()
{
    struct int_array *arr = malloc(sizeof(struct int_array));
    if (!arr) abort();
    int *values = arr->values;

    for (int i = 0; i < 10; i++)
    {
        values[i] = 0;
    }

    return arr;
}

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

// TODO: make this function pass the verification
/***
 * Description:
 * The `dispose_array` function disposes an int_array.
 *
 * @param arr: the given int_array that has the property of int_array
 *
 * The function makes sure that the int_array is freed. 
 */
void dispose_array(struct int_array *arr)
{
    free(arr);
}
