#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

/*@
predicate lseg(struct node *from, struct node *to, int count) =
    from == to ?
        count == 0
    :
        from != 0 &*& from->value |-> _ &*& from->next |-> ?next &*& malloc_block_node(from) &*&
        lseg(next, to, count - 1);

predicate nodes(struct node *node, int count) =
    lseg(node, 0, count);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The list_length function calculates the length of a single linked list iteratively by traversing it in a while loop.

@param node: the starting node of the linkedlist

This function makes sure that the linked list is not changed, and the return value is the length of it.
*/
int list_length(struct node *node)
    //@ requires nodes(node, ?count);
    //@ ensures nodes(node, count) &*& result == count;
{
    int i = 0;
    //@ open nodes(node, count);
    while (node != 0)
        //@ invariant lseg(node, 0, count - i) &*& 0 <= i &*& i <= count;
    {
        //@ open lseg(node, 0, count - i);
        node = node->next;
        i++;
    }
    //@ close lseg(node, 0, count - i);
    //@ close nodes(node, count);
    return i;
}