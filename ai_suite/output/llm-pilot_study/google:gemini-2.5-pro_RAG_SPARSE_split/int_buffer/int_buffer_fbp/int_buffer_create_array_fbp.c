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
    return n == 0? nil : append(zeros(n - 1), cons(0, nil));
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

    for (int i = 0; i < 10; i++)
        /*@
        invariant
            0 <= i &*& i <= 10 &*&
            malloc_block_int_array(arr) &*&
            values == arr->values &*&
            values[0..i] |-> zeros(i) &*&
            values[i..10] |-> _;
        decreases 10 - i;
        @*/
    {
        values[i] = 0;
    }

    return arr;
}