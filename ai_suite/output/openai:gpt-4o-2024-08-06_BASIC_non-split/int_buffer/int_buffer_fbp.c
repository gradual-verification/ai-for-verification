#include <stdlib.h>
#include <stdbool.h>

struct int_array {
    int values[10];
};

/*@
predicate array(struct int_array *arr, list<int> cs) =
    malloc_block_int_array(arr) &*&
    ints(arr->values, 10, cs);
@*/

/*@
fixpoint_auto list<int> zeros(int n) {
    return n == 0? nil : cons(0, zeros(n - 1));
}
@*/

// TODO: make this function pass the verification
struct int_array *create_array()
    //@ requires true;
    //@ ensures array(result, zeros(10));
{
    struct int_array *arr = malloc(sizeof(struct int_array));
    if (!arr) abort();
    //@ open zeros(10);
    //@ close zeros(10);
    //@ ints_to_ints_(arr->values);
    int *values = arr->values;

    for (int i = 0; i < 10; i++)
    //@ invariant ints(values, 10, ?cs) &*& 0 <= i &*& i <= 10 &*& take(i, cs) == zeros(i) &*& drop(i, cs) == drop(i, zeros(10));
    {
        values[i] = 0;
        //@ ints__to_ints(values);
        //@ nth_update(i, 0, cs);
    }

    //@ close array(arr, zeros(10));
    return arr;
}

// TODO: make this function pass the verification
void set(struct int_array *arr, int index, int value)
    //@ requires array(arr, ?elems) &*& 0 <= index && index < 10;
    //@ ensures array(arr, update(index, value, elems));
{
    //@ open array(arr, elems);
    arr->values[index] = value;
    //@ ints__to_ints(arr->values);
    //@ close array(arr, update(index, value, elems));
}

// TODO: make this function pass the verification
int get(struct int_array *arr, int index)
    //@ requires array(arr, ?elems) &*& 0 <= index && index < 10;
    //@ ensures array(arr, elems) &*& result == nth(index, elems);
{
    //@ open array(arr, elems);
    int result = arr->values[index];
    //@ ints__to_ints(arr->values);
    //@ close array(arr, elems);
    return result;
}

// TODO: make this function pass the verification
void dispose_array(struct int_array *arr)
    //@ requires array(arr, _);
    //@ ensures true;
{
    //@ open array(arr, _);
    free(arr);
}