#include <stdlib.h>
#include <stdbool.h>

struct int_array {
    int values[10];
};

/*@
predicate array(struct int_array *arr, list<int> cs) =
    malloc_block_int_array(arr) &*&          /* Heap block that was returned by malloc */
    arr->values[..10] |-> cs;                /* Permission for all 10 elements         */
@*/

/*@
fixpoint_auto list<int> zeros(int n) {
    return n == 0 ? nil : append(zeros(n - 1), cons(0, nil));
}
@*/

// TODO: make this function pass the verification
void dispose_array(struct int_array *arr)
    //@ requires array(arr, _);
    //@ ensures  true;
{
    /* We reveal the predicate so that the required chunks
       (the malloc-block and the permissions for the elements)
       become available to match the contract of free().        */
    //@ open array(arr, _);
    free(arr);
}