#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

/*@
// A predicate to represent a linked list starting at node 'l'.
// 'xs' is a ghost parameter representing the list of integer values.
predicate list(struct node *l; list<int> xs) =
    l == 0 ?
        xs == nil
    :
        l->next |-> ?next &*&
        l->value |-> ?v &*&
        malloc_block_node(l) &*&
        list(next, ?xs_tail) &*&
        xs == cons(v, xs_tail);
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
    //@ requires [?f1]list(n1, ?xs1) &*& [?f2]list(n2, ?xs2);
    //@ ensures [f1]list(n1, xs1) &*& [f2]list(n2, xs2);
{
    while (true)
        //@ invariant [f1]list(n1, xs1) &*& [f2]list(n2, xs2);
    {
        goto l1;
    l2:
        goto l3;
    l1:
        goto l2;
    }
l3:
    // The 'goto l3' statement jumps here, exiting the loop.
    // The function then returns, preserving the state from the precondition.
}