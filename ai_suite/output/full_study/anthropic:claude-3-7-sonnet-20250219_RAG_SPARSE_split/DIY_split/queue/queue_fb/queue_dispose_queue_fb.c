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

void dispose_queue(struct queue *q)
    //@ requires queue(q, 0);
    //@ ensures true;
{
    //@ open queue(q, 0);
    // When count is 0, the tail is 0 (null) according to the queue predicate
    // So we just need to free the queue structure itself
    free(q);
    //@ close true;
}