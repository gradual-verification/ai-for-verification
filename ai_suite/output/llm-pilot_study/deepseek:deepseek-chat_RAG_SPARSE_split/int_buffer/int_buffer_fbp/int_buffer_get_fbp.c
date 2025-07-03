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
    //@ open arr->values[..10] |-> elems;
    //@ ints_split(arr->values, index);
    //@ assert arr->values[index..index+1] |-> ?elemSlice;
    //@ assert arr->values[index+1..10] |-> ?restSlice;
    //@ assert elems == append(take(index, elems), cons(nth(index, elems), drop(index+1, elems)));
    int result = arr->values[index];
    //@ close arr->values[index..index+1] |-> elemSlice;
    //@ close arr->values[index+1..10] |-> restSlice;
    //@ close arr->values[..10] |-> elems;
    //@ close array(arr, elems);
    return result;
}