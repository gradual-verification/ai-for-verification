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
predicate lseg(struct node *from, struct node *to, int count) =
    from == to ?
        count == 0
    :
        count > 0 &*& from->value |-> ?v &*& from->next |-> ?next &*& malloc_block_node(from) &*& lseg(next, to, count - 1);

predicate queue(struct queue *q, int count) =
    q->head |-> ?head &*& q->tail |-> ?tail &*& malloc_block_queue(q) &*&
    (count == 0 ?
        tail == 0
    :
        count > 0 &*& tail != 0 &*& lseg(head, tail, count - 1) &*& tail->value |-> ?v &*& tail->next |-> 0 &*& malloc_block_node(tail));
@*/

int dequeue(struct queue *q)
    //@ requires queue(q, ?count) &*& count > 0;
    //@ ensures queue(q, count - 1);
{
    //@ open queue(q, count);
    struct node *n = q->head;
    int val;

    if (q->head == q->tail) {
        //@ assert q->head |-> n &*& q->tail |-> ?tail &*& n == tail;
        //@ assert tail->value |-> ?v &*& tail->next |-> 0 &*& malloc_block_node(tail);
        val = q->tail->value;
        q->head = 0;
        q->tail = 0;
        //@ assert count == 1;
        //@ assert lseg(n, tail, 0);
        free(n);
        //@ close queue(q, 0);
    } else {
        //@ assert q->head |-> n &*& q->tail |-> ?tail &*& n != tail;
        //@ assert lseg(n, tail, count - 1) &*& tail->value |-> ?v &*& tail->next |-> 0 &*& malloc_block_node(tail);
        //@ open lseg(n, tail, count - 1);
        //@ assert n->value |-> ?nv &*& n->next |-> ?next &*& malloc_block_node(n) &*& lseg(next, tail, count - 2);
        val = n->value;
        struct node *next = n->next;
        q->head = next;
        free(n);
        //@ close queue(q, count - 1);
    }

    return val;
}