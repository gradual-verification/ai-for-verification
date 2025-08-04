#include "prelude.h"

struct node {
    struct node *next;
    int value;
};

/*@
// A predicate representing a list segment from 'from' to 'to'.
// 'values' is a logical list of the integer values in the nodes.
predicate lseg(struct node *from, struct node *to, list<int> values) =
    from == to ?
        values == nil
    :
        from != 0 &*&
        from->next |-> ?next &*&
        from->value |-> ?value &*&
        malloc_block_node(from) &*&
        lseg(next, to, ?tail_values) &*&
        values == cons(value, tail_values);

// A lemma to prove that appending a node to a list segment results in a valid, longer segment.
// This is crucial for verifying the loop invariant.
lemma void lseg_append(struct node *head, struct node *tail)
    requires
        lseg(head, tail, ?vs) &*&
        tail != 0 &*&
        tail->next |-> ?next_node &*&
        tail->value |-> ?v &*&
        malloc_block_node(tail);
    ensures
        lseg(head, next_node, append(vs, cons(v, nil)));
{
    open lseg(head, tail, vs);
    if (head == tail) {
        close lseg(next_node, next_node, nil);
    } else {
        lseg_append(head->next, tail);
    }
    close lseg(head, next_node, append(vs, cons(v, nil)));
}
@*/


// TODO: make this function pass the verification
/***
 * Description:
The list_length function calculates the length of a single linked list iteratively by traversing it in a while loop.

@param node: the starting node of the linkedlist

This function makes sure that the linked list is not changed, and the return valie is the length of it.
*/
int list_length(struct node *node)
    //@ requires lseg(node, 0, ?values);
    //@ ensures lseg(node, 0, values) &*& result == length(values);
{
    //@ struct node *head = node;
    int i = 0;
    //@ close lseg(head, node, nil);
    while (node != 0)
        /*@
        invariant
            lseg(head, node, ?vs_done) &*&
            lseg(node, 0, ?vs_todo) &*&
            values == append(vs_done, vs_todo) &*&
            i == length(vs_done);
        @*/
    {
        //@ open lseg(node, 0, vs_todo);
        struct node *next = node->next;
        //@ lseg_append(head, node);
        //@ append_assoc(vs_done, cons(head(vs_todo), nil), tail(vs_todo));
        node = next;
        i++;
    }
    //@ open lseg(node, 0, vs_todo); // node is 0, so vs_todo is nil
    //@ append_nil(vs_done);
    return i;
}