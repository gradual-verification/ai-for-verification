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

void set(struct int_array *arr, int index, int value)
    //@ requires array(arr, ?elems) &*& 0 <= index && index < 10;
    //@ ensures array(arr, update(index, value, elems));
{
    //@ open array(arr, elems);
    //@ ints_split(arr->values, index);
    //@ open ints(arr->values + index, 10 - index, _);
    arr->values[index] = value;
    //@ close ints(arr->values + index, 10 - index, update(0, value, drop(index, elems)));
    //@ ints_join(arr->values);
    //@ close array(arr, update(index, value, elems));
}