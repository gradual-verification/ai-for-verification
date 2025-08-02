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
void break_test(struct node *n1, struct node *n2)
    //@ requires nodes(n1) &*& nodes(n2);
    //@ ensures nodes(n1) &*& nodes(n2);
{
    //@ open nodes(n1);
    //@ open nodes(n2);
    while (true)
        //@ invariant (n1 == 0 ? true : n1->next |-> ?next1 &*& n1->value |-> _ &*& nodes(next1)) &*& (n2 == 0 ? true : n2->next |-> ?next2 &*& n2->value |-> _ &*& nodes(next2));
    {
        break;
    }
    //@ close nodes(n2);
    //@ close nodes(n1);
}