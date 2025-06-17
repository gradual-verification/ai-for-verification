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
    //@ invariant ints_(values, 10, ?cs) &*& 0 <= i &*& i <= 10 &*& take(i, cs) == zeros(i);
    {
        values[i] = 0;
        //@ chars_to_ints(values, 10);
        //@ assert ints(values, 10, ?cs0);
        //@ ints__to_ints(values);
        //@ assert ints(values, 10, ?cs1);
        //@ assert take(i, cs1) == zeros(i);
        //@ assert drop(i, cs1) == drop(i, zeros(10));
        //@ assert drop(i, cs1) == zeros(10 - i);
        //@ assert cs1 == append(zeros(i), zeros(10 - i));
    }
    //@ assert ints(values, 10, zeros(10));
    //@ close array(arr, zeros(10));
    return arr;
}