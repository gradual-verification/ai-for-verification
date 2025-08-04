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
// A linked list segment from 'from' to 'to' with 'count' nodes.
// The 'to' node is not part of the segment.
predicate lseg(struct node *from, struct node *to, int count) =
    from == to ?
        count == 0
    :
        count > 0 &*& from != 0 &*&
        from->value |-> ?v &*&
        from->next |-> ?next &*&
        malloc_block_node(from) &*&
        lseg(next, to, count - 1);

// A queue data structure.
predicate queue(struct queue *q, int count) =
    q->head |-> ?head &*&
    q->tail |-> ?tail &*&
    malloc_block_queue(q) &*&
    (count == 0 ?
        // An empty queue has null head and tail.
        head == 0 &*& tail == 0
    :
        // A non-empty queue has a list of 'count' nodes.
        count > 0 &*& head != 0 &*& tail != 0 &*&
        lseg(head, tail, count - 1) &*& // A segment from head up to (but not including) tail.
        tail->value |-> ?v &*&
        tail->next |-> 0 &*& // The last node points to null.
        malloc_block_node(tail)); // The tail node is also a malloc'd block.
@*/

// TODO: make this function pass the verification
void dispose_queue(struct queue *q)
    //@ requires queue(q, 0);
    //@ ensures true;
{
    //@ open queue(q, 0);
    free(q);
}