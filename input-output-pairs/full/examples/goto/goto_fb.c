#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

/*@
predicate nodes(struct node *head) =
    head == 0 ? true : head->next |-> ?next &*& nodes(next);
@*/

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

void nested_blocks(struct node *n1, struct node *n2)
    //@ requires nodes(n1) &*& nodes(n2);
    //@ ensures nodes(n1) &*& nodes(n2);
{
    while (true)
    {
        goto l1;
    l2:
        goto l3;
    l1:
        goto l2;
    }
l3:
}

void break_test(struct node *n1, struct node *n2)
    //@ requires nodes(n1) &*& nodes(n2);
    //@ ensures nodes(n1) &*& nodes(n2);
{
    while (true)
    {
        break;
    }
}
