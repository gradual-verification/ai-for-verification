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
