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

lemma void integers_to_chars_(int *arr, int count)
    requires [?f]integers(arr, count, ?cs);
    ensures [f]chars_((void*)arr, count * sizeof(int), ?bytes);
{
    if (count <= 0) {
        close [f]chars_((void*)arr, 0, nil);
    } else {
        open integers(arr, count, cs);
        integer_to_chars_(arr);
        integers_to_chars_(arr + 1, count - 1);
        chars__join((void*)arr);
    }
}
@*/

// TODO: make this function pass the verification
void dispose_array(struct int_array *arr)
    //@ requires array(arr, _);
    //@ ensures true;
{
    //@ open array(arr, _);
    //@ integers_to_chars_(arr->values, 10);
    //@ open malloc_block_int_array(arr);
    free(arr);
}