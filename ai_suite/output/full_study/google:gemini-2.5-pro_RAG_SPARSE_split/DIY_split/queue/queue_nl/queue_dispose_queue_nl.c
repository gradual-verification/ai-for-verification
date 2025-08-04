#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

struct queue {
    struct node *head;
    struct node *tail;
};

/*@

// A predicate for a segment of a singly-linked list representing a queue's content.
// It asserts that 'h' is the head, 't' is the tail, and 'vs' is the list of values.
predicate queue_lseg(struct node *h, struct node *t, list<int> vs) =
    h == 0 ?
        // If the head is null, the list is empty. The tail must also be null.
        t == 0 &*& vs == nil
    :
        // If the head is not null, we own the node 'h'.
        h->value |-> ?v &*& h->next |-> ?n &*& malloc_block_node(h) &*&
        (
            n == 0 ?
                // If this is the last node, the tail 't' must be this node 'h'.
                t == h &*& vs == cons(v, nil)
            :
                // Otherwise, recurse on the rest of the list.
                queue_lseg(n, t, ?tail_vs) &*& vs == cons(v, tail_vs)
        );

// A predicate for a queue struct.
// It asserts ownership of the queue struct and relates its fields to the abstract list of values 'vs'.
predicate queue(struct queue *q, list<int> vs) =
    q->head |-> ?h &*& q->tail |-> ?t &*& malloc_block_queue(q) &*&
    queue_lseg(h, t, vs);

@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `dispose_queue` function frees an empty queue. 
 *
 * @param q: the given empty queue to be freed
 * 
 * It makes sure that q is freed. 
 */
void dispose_queue(struct queue *q)
    //@ requires queue(q, nil);
    //@ ensures true;
{
    //@ open queue(q, nil);
    //@ open queue_lseg(q->head, q->tail, nil);
    free(q);
}