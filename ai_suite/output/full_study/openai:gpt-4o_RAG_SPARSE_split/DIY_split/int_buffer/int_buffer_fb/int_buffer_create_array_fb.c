#include <stdlib.h>
#include <stdbool.h>

struct int_array {
    int values[10];
};

/*@
predicate array(struct int_array *arr, list<int> cs) =
    arr->values[..10] |-> cs;
@*/

/*@
fixpoint_auto list<int> zeros(int n) {
    return n == 0? nil : cons(0, zeros(n - 1));
}
@*/

// TODO: make this function pass the verification
struct int_array *create_array()
    //@ requires true;
    //@ ensures result != 0 ? array(result, zeros(10)) : true;
{
    struct int_array *arr = malloc(sizeof(struct int_array));
    if (!arr) abort();
    int *values = arr->values;

    //@ close ints_(values, 10, _);
    for (int i = 0; i < 10; i++)
    //@ invariant ints_(values, 10, ?vs) &*& 0 <= i &*& i <= 10;
    {
        //@ open ints_(values, 10, vs);
        values[i] = 0;
        //@ close ints_(values, 10, update(i, 0, vs));
    }
    //@ close array(arr, zeros(10));
    return arr;
}