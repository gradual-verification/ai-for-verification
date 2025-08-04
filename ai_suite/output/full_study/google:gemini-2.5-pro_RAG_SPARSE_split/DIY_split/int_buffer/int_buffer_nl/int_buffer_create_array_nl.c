#include <stdlib.h>
#include <stdbool.h>

struct int_array {
    int values[10];
};

/*@
fixpoint list<int> zeros(int n) {
    return n <= 0 ? nil : cons(0, zeros(n - 1));
}

predicate int_array(struct int_array *arr; list<int> vs) =
    ints(arr->values, 10, vs) &*&
    malloc_block_int_array(arr);
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `create_array` function creates an int_array with its values as 10 zeros.
 *
 * It makes sure that the new int_array has 10 zeros in its value. 
 */
struct int_array *create_array()
    //@ requires true;
    //@ ensures int_array(result, zeros(10));
{
    struct int_array *arr = malloc(sizeof(struct int_array));
    if (!arr) abort();
    int *values = arr->values;

    for (int i = 0; i < 10; i++)
        //@ invariant 0 <= i &*& i <= 10 &*& arr->values |-> values &*& malloc_block_int_array(arr) &*& ints(values, i, zeros(i)) &*& ints_(values + i, 10 - i, _);
    {
        values[i] = 0;
    }

    return arr;
}