#include "stdlib.h"

struct node {
    struct node *next;
    int          value;
};

struct queue {
    struct node *head;
    struct node *tail;
};

/*@
predicate lseg(struct node *from, struct node *to, int count) =
    from == to ?
        count == 0
    :
        count > 0 &*&
        from->value |-> ?v  &*&
        from->next  |-> ?n  &*&
        malloc_block_node(from) &*&
        lseg(n, to, count - 1);

predicate queue(struct queue *q, int count) =
    q->head |-> ?h &*&
    q->tail |-> ?t &*&
    malloc_block_queue(q) &*&
    ( count == 0
      ? t == 0                                        // empty queue: tail is NULL
      : count > 0 &*&
        t   != 0 &*&
        lseg(h, t, count - 1) &*&                     // all nodes but the tail
        t->value |-> ?v &*& t->next |-> 0 &*& malloc_block_node(t)
    );
@*/


/*  dispose_queue
    --------------
    For an empty queue (count == 0) the predicate gives us
        - the two field chunks  q->head |-> h   and  q->tail |-> 0
        - the malloc-block      malloc_block_queue(q)

    These chunks are exactly what is needed to call free(q):  free consumes
    the malloc_block chunk together with all field chunks stored in the
    block.  No nodes have to be disposed because the queue is empty.
*/
// verified
void dispose_queue(struct queue *q)
    //@ requires queue(q, 0);
    //@ ensures  true;
{
    //@ open queue(q, 0);      // expose the field chunks and malloc_block
    free(q);                   // consumes them
}