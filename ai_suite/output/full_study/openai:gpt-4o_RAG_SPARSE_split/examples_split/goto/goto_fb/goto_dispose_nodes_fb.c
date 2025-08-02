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
void dispose_nodes(struct node *head)
    //@ requires nodes(head);
    //@ ensures true;
{
    while (head != 0)
        //@ invariant nodes(head);
    {
        struct node *next = head->next;
        //@ open nodes(head);
        free(head);
        head = next;
    }
}