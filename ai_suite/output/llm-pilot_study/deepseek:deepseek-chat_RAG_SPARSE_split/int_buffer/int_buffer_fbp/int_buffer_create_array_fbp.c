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
fixpoint list<int> zeros(int n) {
    return n == 0 ? nil : cons(0, zeros(n - 1));
}
@*/

struct int_array *create_array()
    //@ requires true;
    //@ ensures array(result, zeros(10));
{
    struct int_array *arr = malloc(sizeof(struct int_array));
    if (!arr) abort();
    int *values = arr->values;

    //@ close arr->values[0..10] |-> zeros(10);
    for (int i = 0; i < 10; i++)
        //@ invariant arr->values[i..10] |-> zeros(10 - i);
    {
        values[i] = 0;
        //@ open arr->values[i..10] |-> zeros(10 - i);
        //@ close arr->values[i+1..10] |-> zeros(10 - (i + 1));
        //@ close arr->values[i..10] |-> cons(0, zeros(10 - (i + 1)));
    }
    //@ open arr->values[10..10] |-> zeros(0);
    //@ close array(arr, zeros(10));
    return arr;
}