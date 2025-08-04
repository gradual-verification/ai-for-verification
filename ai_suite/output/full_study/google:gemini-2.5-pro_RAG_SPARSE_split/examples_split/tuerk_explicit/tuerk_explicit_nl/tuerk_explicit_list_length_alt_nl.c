#include "stdlib.h"
#include "prelude.h"

struct node {
    struct node *next;
    int value;
};

/*@

// A predicate representing a list segment from 'from' to 'to'.
// 'vs' is a ghost parameter representing the sequence of integer values in the segment.
predicate lseg(struct node *from, struct node *to, list<int> vs) =
    from == to ?
        vs == nil
    :
        from != 0 &*&
        from->value |-> ?v &*&
        from->next |-> ?next &*&
        malloc_block_node(from) &*&
        lseg(next, to, ?tail_vs) &*&
        vs == cons(v, tail_vs);

// A predicate for a standard, null-terminated linked list.
predicate list(struct node *head, list<int> vs) =
    lseg(head, 0, vs);

// A lemma to convert a 'list' predicate into an 'lseg' predicate.
// This is useful for transitioning from the function's precondition to the loop invariant.
lemma void list_to_lseg(struct node *head)
    requires list(head, ?vs);
    ensures lseg(head, 0, vs);
{
    open list(head, vs);
}

// A lemma to convert an 'lseg' predicate back into a 'list' predicate.
// This is useful for establishing the function's postcondition after the loop.
lemma void lseg_to_list(struct node *head)
    requires lseg(head, 0, ?vs);
    ensures list(head, vs);
{
    close list(head, vs);
}

// A lemma to "move" a node from the beginning of one list segment
// to the end of another. This is the core transformation needed inside the loop.
lemma void lseg_append_node(struct node *first)
    requires lseg(first, ?last, ?vs1) &*& last != 0 &*& last->value |-> ?v &*& last->next |-> ?next &*& malloc_block_node(last) &*& lseg(next, 0, ?vs2);
    ensures lseg(first, next, append(vs1, cons(v, nil))) &*& lseg(next, 0, vs2);
{
    open lseg(first, last, vs1);
    if (first == last) {
        close lseg(next, next, nil);
    } else {
        lseg_append_node(first->next);
    }
    open lseg(next, 0, vs2);
    close lseg(next, 0, vs2);
    close lseg(first, next, append(vs1, cons(v, nil)));
}

@*/


// TODO: make this function pass the verification
/***
 * Description:
The list_length_alt function calculates the length of a single linked list iteratively by traversing it in a for loop.

@param node: the starting node of the linkedlist

This function makes sure that the linked list is not changed, and the return valie is the length of it.
*/
int list_length_alt(struct node *node)
    //@ requires list(node, ?vs) &*& length(vs) <= INT_MAX;
    //@ ensures list(node, vs) &*& result == length(vs);
{
    //@ struct node *original_node = node;
    //@ list_to_lseg(original_node);
    //@ close lseg(original_node, original_node, nil);
    int i;
    for (i = 0; node != 0; node = node->next, i++)
        /*@
        invariant
            lseg(original_node, node, ?vs_done) &*&
            lseg(node, 0, ?vs_todo) &*&
            vs == append(vs_done, vs_todo) &*&
            i == length(vs_done) &*&
            length(vs) <= INT_MAX;
        @*/
    {
        //@ open lseg(node, 0, vs_todo);
        //@ lseg_append_node(original_node);
        //@ append_assoc(vs_done, cons(head(vs_todo), nil), tail(vs_todo));
    }
    //@ open lseg(node, 0, vs_todo); // After the loop, node is 0, so vs_todo is nil.
    //@ lseg_to_list(original_node);
    return i;
}