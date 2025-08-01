#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

/*@
predicate nodes(struct node *head) =
    head == 0 ? true : head->next |-> ?next &*& head->value |-> _ &*& nodes(next);
@*/


// TODO: make this function pass the verification
void dispose_nodes(struct node *head)
    //@ requires nodes(head);
    //@ ensures true;
{
loop:
    if (head == 0) return;
    struct node *next = head->next;
    free(head);
    head = next;
    goto loop;
}

