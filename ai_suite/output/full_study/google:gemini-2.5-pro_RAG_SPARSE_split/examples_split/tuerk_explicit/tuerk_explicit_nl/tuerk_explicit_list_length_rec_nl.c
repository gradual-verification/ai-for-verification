#include "prelude.h"

struct node {
    struct node *next;
    int value;
};

/*@
// A predicate to describe a singly-linked list starting at 'n'.
// 'values' is a ghost parameter representing the sequence of integers in the list.
predicate list_pred(struct node *n, list<int> values) =
    n == 0 ?
        // An empty list corresponds to a null pointer.
        values == nil
    :
        // A non-empty list has a value and a pointer to the next node.
        n->value |-> ?v &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        // The rest of the list is described recursively.
        list_pred(next, ?tail) &*&
        // The full list of values is the head's value prepended to the tail's values.
        values == cons(v, tail);
@*/


/***
 * Description:
The list_length_rec function calculates the length of a single linked list recursively.

@param node: the starting node of the linkedlist

This function makes sure that the linked list is not changed, and the return valie is the length of it.
*/
int list_length_rec(struct node *node)
    //@ requires list_pred(node, ?values);
    //@ ensures list_pred(node, values) &*& result == length(values);
{
    if (node == 0) {
        //@ open list_pred(node, values); // In this branch, node == 0, so values == nil.
        //@ close list_pred(0, nil);     // Re-establish the predicate for the null list.
        return 0;
    } else {
        //@ open list_pred(node, values); // Expose node->next for the recursive call.
        int length0 = list_length_rec(node->next);
        // The recursive call ensures: list_pred(node->next, tail) and length0 == length(tail)
        //@ close list_pred(node, values); // Re-establish the predicate for the full list.
        return 1 + length0;
    }
}