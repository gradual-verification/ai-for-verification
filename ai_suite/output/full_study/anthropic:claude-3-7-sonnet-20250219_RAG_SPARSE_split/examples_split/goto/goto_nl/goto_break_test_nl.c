#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

/*@
// Define a predicate for a node
predicate node(struct node *n; struct node *next, int value) =
    n != 0 &*&
    n->next |-> next &*&
    n->value |-> value &*&
    malloc_block_node(n);

// Define a predicate for a null node
predicate node_null(struct node *n) =
    n == 0;
@*/

// TODO: make this function pass the verification
/***
 * Description:
The break_test function tests whether the break statement can get out of the while loop,
and it doesn't modify the given parameters.

@param n1, n2: nodes unchanged in this function

It makes sure that n1 and n2 are unchanged. 
*/
void break_test(struct node *n1, struct node *n2)
//@ requires (n1 == 0 ? node_null(n1) : node(n1, ?next1, ?value1)) &*& (n2 == 0 ? node_null(n2) : node(n2, ?next2, ?value2));
//@ ensures (n1 == 0 ? node_null(n1) : node(n1, next1, value1)) &*& (n2 == 0 ? node_null(n2) : node(n2, next2, value2));
{
    while (true)
    //@ invariant (n1 == 0 ? node_null(n1) : node(n1, next1, value1)) &*& (n2 == 0 ? node_null(n2) : node(n2, next2, value2));
    {
        break;
    }
}