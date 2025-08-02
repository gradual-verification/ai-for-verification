#include "stdlib.h"

struct node {
    struct node *next;
    void *key;
    void *value;
};

struct foo {
    int value;
};

//@ predicate foo(struct foo *f; int v) = f->value |-> v &*& malloc_block_foo(f);

// TODO: make this function pass the verification
/**
 * Description:
 * The `foo_equals` function compares two foo structures for equality based on their `value` members.
 *
 * @param f1 Pointer to the first foo structure.
 * @param f2 Pointer to the second foo structure.
 * @return True if the `value` members of the two foo structures are equal, otherwise false.
 */
//@ requires foo(f1, ?v1) &*& foo(f2, ?v2);
//@ ensures foo(f1, v1) &*& foo(f2, v2) &*& result == (v1 == v2);
bool foo_equals(struct foo *f1, struct foo *f2)
{
    return f1->value == f2->value;
}