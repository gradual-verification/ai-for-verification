#include <stdlib.h>
#include <stdbool.h>

struct int_array {
    int values[10];
};

/***
 * Description:
 * The `fill_zeros` function fills array[i,..n] with 0. 
 * 
 * @param arr: the integer array to be filled
 * @param i: the starting index (inclusive) to be filled, (i >= 0)
 * @param n: the ending index (exclusive) to be filled (i <= n)
 * 
 * It makes sure that the new array has 0s in array[i,..n]. 
 */
void fill_zeros(int *arr, int i, int n)
{
    if (i == n) {
    } else {
        arr[i] = 0;
        fill_zeros(arr, i + 1, n);
    }
}

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
    fill_zeros(arr->values, 0, 10);
    return arr;
}

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
