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
// Corrected lseg predicate: Added malloc_block_node(from) to account for memory ownership of each node.
predicate lseg(struct node *from, struct node *to, int count) =
    from == to ?
        count == 0
    :
        count > 0 &*& from->value |-> ?v &*& from->next |-> ?next &*& malloc_block_node(from) &*& lseg(next, to, count - 1);

// Corrected queue predicate for robustness and verifiability:
// 1. Added malloc_block_queue(q) for the queue struct itself.
// 2. In the empty case (count == 0), require both head and tail to be null for a consistent state.
// 3. In the non-empty case, added malloc_block_node(tail) for the tail node.
predicate queue(struct queue *q, int count) =
    q->head |-> ?head &*& q->tail |-> ?tail &*& malloc_block_queue(q) &*&
    (count == 0 ?
        head == 0 &*& tail == 0
    :
        count > 0 &*& tail != 0 &*& lseg(head, tail, count - 1) &*& tail->value |-> ?v &*& tail->next |-> 0 &*& malloc_block_node(tail));
@*/

// TODO: make this function pass the verification
int dequeue(struct queue *q)
    //@ requires queue(q, ?count) &*& count > 0;
    //@ ensures queue(q, count - 1);
{
    //@ open queue(q, count);
    struct node *n = q->head;
    int val;

    if (q->head == q->tail) {
        // If head == tail and count > 0, then lseg(head, tail, count - 1) implies count - 1 == 0, so count == 1.
        // The chunks for the single node 'n' are provided by the 'tail' part of the queue predicate.
        //@ open lseg(n, q->tail, count - 1);
        val = q->tail->value;
        q->head = 0;
        q->tail = 0;
        free(n);
    } else {
        // If head != tail, then count - 1 > 0, so count > 1.
        // We need to open the lseg to access the fields of the head node 'n'.
        //@ open lseg(n, q->tail, count - 1);
        val = n->value;
        struct node *next = n->next;
        q->head = next;
        free(n);
    }

    //@ close queue(q, count - 1);
    return val;
}