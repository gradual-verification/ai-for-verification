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
// A linked list segment from 'from' to 'to' (exclusive of 'to').
// 'count' is the number of nodes in the segment.
predicate lseg(struct node *from, struct node *to, int count) =
    from == to ?
        count == 0
    :
        count > 0 &*& from != 0 &*&
        from->value |-> ?v &*&
        from->next |-> ?next &*&
        malloc_block_node(from) &*&
        lseg(next, to, count - 1);

// A queue with 'count' elements.
predicate queue(struct queue *q, int count) =
    q->head |-> ?head &*& q->tail |-> ?tail &*& malloc_block_queue(q) &*&
    (count == 0 ?
        // An empty queue has null head and tail.
        head == 0 &*& tail == 0
    :
        // A non-empty queue has a list segment from head to tail (exclusive),
        // and the tail node is owned separately.
        count > 0 &*& tail != 0 &*&
        lseg(head, tail, count - 1) &*&
        tail->value |-> ?v &*&
        tail->next |-> 0 &*&
        malloc_block_node(tail));
@*/

// TODO: make this function pass the verification
struct queue *create_queue()
    //@ requires true;
    //@ ensures queue(result, 0);
{
    struct queue *q = malloc(sizeof(struct queue));
    if (q == 0) abort();
    q->head = 0;
    q->tail = 0;
    //@ close queue(q, 0);
    return q;
}