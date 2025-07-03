#include <stdlib.h>
#include <stdbool.h>

struct int_array {
    int values[10];
};

/*@
predicate array(struct int_array *arr, list<int> cs) =
    malloc_block_int_array(arr) &*&
    arr->values[..10] |-> cs;
@*/

/*@
fixpoint_auto list<int> zeros(int n) {
    return n == 0 ? nil : cons(0, zeros(n - 1));
}
@*/

// TODO: make this function pass the verification
struct int_array *create_array()
    //@ requires true;
    //@ ensures array(result, zeros(10));
{
    struct int_array *arr = malloc(sizeof(struct int_array));
    if (!arr) abort();
    int *values = arr->values;

    //@ close ints_(values, 10, _);
    for (int i = 0; i < 10; i++)
    //@ invariant ints_(values, 10, ?cs) &*& 0 <= i &*& i <= 10;
    {
        values[i] = 0;
        //@ close ints_(values + i, 1, cons(0, nil));
        //@ ints__split(values, i + 1);
    }
    //@ close array(arr, zeros(10));
    return arr;
}