#include "stdlib.h"

struct node {
    struct node *next;
    void *key;
    void *value;
};

struct foo {
    int value;
};


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
{
    
    return f1->value == f2->value;
   
}

