#include <stdlib.h>
#include <stdbool.h>

struct int_array {
    int values[10];
};

/*@
// Define a predicate for the int_array structure
predicate int_array(struct int_array *arr; list<int> vs) =
    arr != 0 &*&
    malloc_block_int_array(arr) &*&
    ints(arr->values, 10, vs) &*&
    length(vs) == 10;
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `create_array` function creates an int_array with its values as 10 zeros.
 *
 * It makes sure that the new int_array has 10 zeros in its value. 
 */
/*@
// Function contract
requires true;
ensures int_array(result, ?vs) &*& all_eq(vs, 0) == true;
@*/
struct int_array *create_array()
{
    struct int_array *arr = malloc(sizeof(struct int_array));
    if (!arr) abort();
    int *values = arr->values;

    //@ close ints(values, 0, nil);
    for (int i = 0; i < 10; i++)
        /*@
        invariant 0 <= i &*& i <= 10 &*&
                 ints(values, i, ?vs_init) &*&
                 length(vs_init) == i &*&
                 all_eq(vs_init, 0) == true;
        @*/
    {
        values[i] = 0;
        //@ close ints(values + i, 1, cons(0, nil));
        //@ ints_join(values);
    }
    //@ assert ints(values, 10, ?final_vs);
    //@ assert all_eq(final_vs, 0) == true;
    //@ close int_array(arr, final_vs);
    return arr;
}