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
void nested_blocks(struct node *n1, struct node *n2)
    //@ requires nodes(n1) &*& nodes(n2);
    //@ ensures nodes(n1) &*& nodes(n2);
{
    //@ open nodes(n1);
    //@ open nodes(n2);
    //@ close nodes(n1);
    //@ close nodes(n2);
    
    while (true)
        //@ invariant nodes(n1) &*& nodes(n2);
    {
        goto l1;
    l2:
        goto l3;
    l1:
        goto l2;
    }
l3:
    //@ // We've reached the end, and the invariant still holds
}