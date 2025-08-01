#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

/*@
predicate nodes(struct node *head) =
    head == 0 ? true : head->next |-> ?next &*& head->value |-> _ &*& malloc_block_node(head) &*& nodes(next);
@*/


// TODO: make this function pass the verification
void break_test(struct node *n1, struct node *n2)
    //@ requires nodes(n1) &*& nodes(n2);
    //@ ensures nodes(n1) &*& nodes(n2);
{
    while (true)
    {
        break;
    }
}
