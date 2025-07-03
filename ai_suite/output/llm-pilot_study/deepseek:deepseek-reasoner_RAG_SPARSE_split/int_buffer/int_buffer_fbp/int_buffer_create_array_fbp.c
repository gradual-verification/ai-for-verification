#include <stdlib.h>
#include <stdbool.h>

struct int_array {
    int values[10];
};

/*@
predicate array(struct int_array *arr, list<int> cs) =
    malloc_block_int_array(arr) &*&
    arr->values[..10] |-> cs;

fixpoint_auto list<int> zeros(int n) {
    return n == 0? nil : append(zeros(n - 1), cons(0, nil));
}

lemma_auto void zeros_append(int n)
    requires 0 <= n;
    ensures append(zeros(n), cons(0, nil)) == zeros(n + 1);
{
    if (n == 0) {
        // trivial
    } else {
        zeros_append(n - 1);
    }
}
@*/

struct int_array *create_array()
    //@ requires true;
    //@ ensures array(result, zeros(10));
{
    struct int_array *arr = malloc(sizeof(struct int_array));
    if (!arr) abort();
    int *values = arr->values;

    //@ close integers(arr->values, 0, nil);
    for (int i = 0; i < 10; i++)
        /*@
        invariant integers(arr->values, i, zeros(i)) &*&
                  integers_(arr->values + i, 10 - i, ?rest);
        @*/
    {
        //@ open integers_(arr->values + i, 10 - i, rest);
        values[i] = 0;
        //@ close integer(arr->values + i, 0);
        //@ close integers(arr->values + i, 1, cons(0, nil));
        //@ integers_join(arr->values);
        //@ zeros_append(i);
    }
    //@ open integers_(arr->values + 10, 0, _);
    //@ close array(arr, zeros(10));
    return arr;
}