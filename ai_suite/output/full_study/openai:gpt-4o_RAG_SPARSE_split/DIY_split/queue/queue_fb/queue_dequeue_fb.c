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
        count > 0 &*& from->value |-> ?v &*& from->next |-> ?next &*& lseg(next, to, count - 1);

predicate queue(struct queue *q, int count) =
    q->head |-> ?head &*& q->tail |-> ?tail &*&
    (count == 0 ?
        tail == 0
    :
        count > 0 &*& tail != 0 &*& lseg(head, tail, count - 1) &*& tail->value |-> ?v &*& tail->next |-> 0);
@*/

int dequeue(struct queue *q)
    //@ requires queue(q, ?count) &*& count > 0;
    //@ ensures queue(q, count - 1);
{
    struct node *n = q->head;
    int val;

    if (q->head == q->tail) {
        val = q->tail->value;
        q->head = 0;
        q->tail = 0;
        //@ open lseg(n, q->tail, count - 1);
        //@ open lseg(q->tail, q->tail, 0);
        //@ close lseg(q->tail, q->tail, 0);
        //@ close lseg(n, q->tail, count - 1);
        free(n);
    } else {
        val = n->value;
        struct node *next = n->next;
        q->head = next;
        //@ open lseg(n, q->tail, count - 1);
        //@ close lseg(next, q->tail, count - 2);
        free(n);
    }

    return val;
}