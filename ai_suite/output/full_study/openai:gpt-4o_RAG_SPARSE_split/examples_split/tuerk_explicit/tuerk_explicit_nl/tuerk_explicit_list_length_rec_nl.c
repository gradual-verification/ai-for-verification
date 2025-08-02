#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

/*@
predicate lseg(struct node *from, struct node *to, list<int> values) =
    from == to ?
        values == nil
    :
        from != 0 &*& from->value |-> ?v &*& from->next |-> ?n &*& malloc_block_node(from) &*&
        lseg(n, to, ?vs) &*& values == cons(v, vs);

predicate nodes(struct node *node, int count) =
    lseg(node, 0, ?values) &*& length(values) == count;
@*/

// TODO: make this function pass the verification
/***
 * Description:
The list_length_rec function calculates the length of a single linked list recursively.

@param node: the starting node of the linkedlist

This function makes sure that the linked list is not changed, and the return value is the length of it.
*/
int list_length_rec(struct node *node)
    //@ requires nodes(node, ?count);
    //@ ensures nodes(node, count) &*& result == count;
{
    //@ open nodes(node, count);
    if (node == 0) {
        //@ close nodes(0, 0);
        return 0;
    } else {
        int length0 = list_length_rec(node->next);
        //@ close nodes(node, count);
        return 1 + length0;
    }
}