#include <stdlib.h>
#include <stdbool.h>

/* ============================================================================
   Data type and abstract array predicate
   ========================================================================== */
struct int_array {
    int values[10];
};

/*@
predicate array(struct int_array *arr, list<int> cs) =
    malloc_block_int_array(arr) &*&        // memory block that holds the struct
    arr->values[..10] |-> cs;              // concrete contents (10 elements)
@*/

/* ============================================================================
   Small list lemma that we will need in ‘set’
   ========================================================================== */
/*@
lemma void update_drop_take_int(int i, int v, list<int> xs)
    requires 0 <= i &*& i < length(xs);
    ensures  update(i, v, xs)
          == append(take(i, xs), cons(v, drop(i + 1, xs)));
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (i == 0) {
            } else {
                update_drop_take_int(i - 1, v, t);
            }
    }
}
@*/

/* ============================================================================
   Function under verification
   ========================================================================== */
void set(struct int_array *arr, int index, int value)
    //@ requires array(arr, ?elems) &*& 0 <= index && index < 10;
    //@ ensures  array(arr, update(index, value, elems));
{
    /* Unfold the array predicate so we can work with the underlying
       ints-chunk representing the contents of the C array. */
    //@ open array(arr, elems);

    /* Split off the prefix [0 .. index-1] and the suffix
       [index .. 9] so that we can isolate the element that is to be
       overwritten.                                                        */
    //@ ints_split(arr->values, index);                          // prefix / suffix
    //@ assert ints(arr->values + index, 10 - index, ?suf1);

    //@ ints_split(arr->values + index, 1);                      // element / rest
    //@ assert ints(arr->values + index, 1, ?oneElem);
    //@ open ints(arr->values + index, 1, oneElem);
    //@ assert integer(arr->values + index, ?oldVal);

    /* Perform the actual write.  VeriFast now knows that we have the
       necessary permission for that single element. */
    arr->values[index] = value;

    /* Close the single-element chunk again, now with the updated value. */
    //@ close integer(arr->values + index, value);
    //@ close ints(arr->values + index, 1, cons(value, nil));

    /* Join the three pieces back together:                                */
    //@ ints_join(arr->values + index);            // join element & rest
    //@ ints_join(arr->values);                    // join prefix  & suffix

    /* At this point we have an ints-chunk for the whole array again.
       Its value list is                 append(take(index, elems),
                                               cons(value,
                                                    drop(index+1, elems)))
       which we show equal to update(index, value, elems).               */
    //@ update_drop_take_int(index, value, elems);

    /* Finally fold back the high-level array predicate. */
    //@ close array(arr, update(index, value, elems));
}

/* ============================================================================
   (Optional) tiny smoke-test – **not required for verification** but handy
   ========================================================================== */
/*
int main() //@ : main
    //@ requires true;
    //@ ensures  true;
{
    struct int_array *a = malloc(sizeof(struct int_array));
    if (a == 0) abort();
    //@ close array(a, zeros(10));
    set(a, 3, 42);
    //@ open array(a, ?vals);
    //@ assert nth(3, vals) == 42;
    //@ close array(a, vals);
    free(a);
    return 0;
}
*/