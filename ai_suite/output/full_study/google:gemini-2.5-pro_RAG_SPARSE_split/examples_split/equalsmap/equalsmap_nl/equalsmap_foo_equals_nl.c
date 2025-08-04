#include "stdlib.h"
#include "stdbool.h"

struct node {
    struct node *next;
    void *key;
    void *value;
};

struct foo {
    int value;
};

/*@
// A predicate to represent a foo struct in the heap.
// 'f' is an input parameter (the pointer to the struct).
// 'v' is an output parameter (the logical value of the struct's member).
// The semicolon makes this a "precise" predicate, allowing VeriFast to merge
// fractional permissions.
predicate foo(struct foo *f; int v) =
    f->value |-> v &*&
    malloc_block_foo(f);
@*/

// TODO: make this function pass the verification
/**
 * Description:
 * The `foo_equals` function compares two foo structures for equality based on their `value` members.
 *
 * @param f1 Pointer to the first foo structure.
 * @param f2 Pointer to the second foo structure.
 * @return True if the `value` members of the two foo structures are equal, otherwise false.
 */
bool foo_equals(struct foo *f1, struct foo *f2)
    /*@
    requires
        // The caller must provide fractional ownership of two foo structs.
        // VeriFast will bind their logical values to v1 and v2.
        [?f1_frac]foo(f1, ?v1) &*&
        [?f2_frac]foo(f2, ?v2);
    ensures
        // The function returns the ownership of the foo structs unchanged.
        [f1_frac]foo(f1, v1) &*&
        [f2_frac]foo(f2, v2) &*&
        // The result of the function is true if and only if the logical values are equal.
        result == (v1 == v2);
    @*/
{
    // VeriFast automatically opens the foo predicates to verify the field accesses
    // and closes them to satisfy the postcondition.
    return f1->value == f2->value;
}