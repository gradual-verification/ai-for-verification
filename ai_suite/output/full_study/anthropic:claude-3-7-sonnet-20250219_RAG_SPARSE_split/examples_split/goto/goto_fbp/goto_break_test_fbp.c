#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

/*@
predicate nodes(struct node *head) =
    head == 0 ? true : head->next |-> ?next &*& head->value |-> _ &*& malloc_block_node(head) &*& nodes(next);
@*/

void break_test(struct node *n1, struct node *n2)
    //@ requires nodes(n1) &*& nodes(n2);
    //@ ensures nodes(n1) &*& nodes(n2);
{
    //@ open nodes(n1);
    //@ open nodes(n2);
    
    while (true)
        //@ invariant (n1 == 0 ? true : n1->next |-> ?next1 &*& n1->value |-> _ &*& malloc_block_node(n1) &*& nodes(next1)) &*& (n2 == 0 ? true : n2->next |-> ?next2 &*& n2->value |-> _ &*& malloc_block_node(n2) &*& nodes(next2));
    {
        break;
    }
    
    //@ close nodes(n1);
    //@ close nodes(n2);
}