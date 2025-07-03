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

int get(struct int_array *arr, int index)
    //@ requires array(arr, ?elems) &*& 0 <= index && index < 10;
    //@ ensures array(arr, elems) &*& result == nth(index, elems);
{
    //@ open array(arr, elems);
    //@ ints_split(arr->values, index);
    //@ ints_split(arr->values + index, 1);
    //@ open ints(arr->values + index, 1, ?oneElement);
    int result = arr->values[index];
    //@ close ints(arr->values + index, 1, oneElement);
    //@ ints_join(arr->values + index);
    //@ ints_join(arr->values);
    //@ close array(arr, elems);
    return result;
}