#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

/*@
predicate nodes(struct node *n, int count) =
    n == 0 ?
        count == 0
    :
        n->next |-> ?next &*& n->value |-> _ &*& malloc_block_node(n) &*& nodes(next, count - 1);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The list_length_alt function calculates the length of a single linked list iteratively by traversing it in a for loop.

@param node: the starting node of the linkedlist

This function makes sure that the linked list is not changed, and the return value is the length of it.
*/
int list_length_alt(struct node *node)
    //@ requires nodes(node, ?count);
    //@ ensures nodes(node, count) &*& result == count;
{
    int i;
    //@ open nodes(node, count);
    for (i = 0; node != 0; node = node->next, i++)
        //@ invariant nodes(node, ?remaining) &*& i + remaining == count;
    {
        //@ open nodes(node, remaining);
    }
    //@ close nodes(node, 0);
    return i;
}