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
    int *values = arr->values;

    for (int i = 0; i < 10; i++)
    //@ invariant array(arr, ?elems) &*& 0 <= i &*& i <= 10 &*& take(i, elems) == zeros(i);
    {
        values[i] = 0;
        //@ close array(arr, update(i, 0, elems));
    }

    return arr;
}

// TODO: make this function pass the verification
void set(struct int_array *arr, int index, int value)
    //@ requires array(arr, ?elems) &*& 0 <= index && index < 10;
    //@ ensures array(arr, update(index, value, elems));
{
    arr->values[index] = value;
    //@ close array(arr, update(index, value, elems));
}

// TODO: make this function pass the verification
int get(struct int_array *arr, int index)
    //@ requires array(arr, ?elems) &*& 0 <= index && index < 10;
    //@ ensures array(arr, elems) &*& result == nth(index, elems);
{
    return arr->values[index];
}

// TODO: make this function pass the verification
void dispose_array(struct int_array *arr)
    //@ requires array(arr, _);
    //@ ensures true;
{
    free(arr);
}