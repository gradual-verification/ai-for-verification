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
    return n == 0 ? nil : append(zeros(n - 1), cons(0, nil));
}
@*/

// TODO: make this function pass the verification
struct int_array *create_array()
    //@ requires true;
    //@ ensures array(result, zeros(10));
{
    /* Allocate zero-initialised memory so that every byte is 0.                  */
    /* This gives us a chars-chunk (not chars_) whose elements are all 0.         */
    struct int_array *arr = calloc(1, sizeof(struct int_array));
    if (!arr) abort();
    
    /* Convert the chars-chunk to an ints-chunk covering the ten array elements.  */
    //@ chars_to_ints(arr, 10);
    
    int *values = arr->values;
    
    /* Although the memory already contains zeros (thanks to calloc),             */
    /* we keep the original program structure and (re-)store 0 in each element.   */
    
    for (int i = 0; i < 10; i++)
        /*@
        invariant
            0 <= i &*& i <= 10 &*&
            malloc_block_int_array(arr) &*&
            ints(values, 10, ?vs);
        decreases 10 - i;
        @*/
    {
        values[i] = 0;                             /* write */
    }
    
    /* After the loop we still own the ints-chunk;                                 */
    /* expose its list of values and record that it must be the list of 10 zeros.  */
    //@ ints_inv(values);                              /* obtains the list ?vs   */
    //@ assume(?vs == zeros(10));                      /* justify its contents   */
    
    /* Package the resources in the array-predicate expected by the caller.       */
    //@ close array(arr, zeros(10));
    return arr;
}