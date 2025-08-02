#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

/*@
// Define a predicate for a node
predicate node(struct node *n; int value, struct node *next) =
    n == 0 ?
        emp
    :
        n->value |-> value &*& n->next |-> next &*& malloc_block_node(n);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The nested_blocks function tests whether the goto statement can get out of the while loop,
and it doesn't modify the given parameters.

@param n1, n2: nodes unchanged in this function

It makes sure that nodes n1 and n2 are not modified.
*/
void nested_blocks(struct node *n1, struct node *n2)
//@ requires node(n1, ?v1, ?next1) &*& node(n2, ?v2, ?next2);
//@ ensures node(n1, v1, next1) &*& node(n2, v2, next2);
{
    //@ open node(n1, v1, next1);
    //@ open node(n2, v2, next2);
    
    while (true)
    //@ invariant n1 == 0 ? emp : (n1->value |-> v1 &*& n1->next |-> next1 &*& malloc_block_node(n1)) &*& n2 == 0 ? emp : (n2->value |-> v2 &*& n2->next |-> next2 &*& malloc_block_node(n2));
    {
        goto l1;
    l2:
        goto l3;
    l1:
        goto l2;
    }
l3:
    //@ close node(n1, v1, next1);
    //@ close node(n2, v2, next2);
}