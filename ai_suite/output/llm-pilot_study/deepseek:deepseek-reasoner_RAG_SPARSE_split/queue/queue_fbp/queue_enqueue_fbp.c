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

lemma void lseg_add(struct node *first, struct node *last)
    requires lseg(first, last, ?n) &*& last != 0 &*& last->value |-> ?v &*& last->next |-> ?next &*& malloc_block_node(last) &*& next == 0;
    ensures lseg(first, next, n + 1) &*& next->value |-> ?new_v &*& next->next |-> 0 &*& malloc_block_node(next);
{
    open lseg(first, last, n);
    if (first == last) {
        close lseg(next, next, 0);
    } else {
        lseg_add(first->next, last);
    }
    close lseg(first, next, n + 1);
}

predicate queue(struct queue *q, int count) =
    q->head |-> ?head &*& q->tail |-> ?tail &*& malloc_block_queue(q) &*&
    (count == 0 ?
        tail == 0
    :
        count > 0 &*& tail != 0 &*& lseg(head, tail, count - 1) &*& tail->value |-> ?v &*& tail->next |-> 0 &*& malloc_block_node(tail));
@*/

void enqueue(struct queue *q, int val)
    //@ requires queue(q, ?count);
    //@ ensures queue(q, count + 1);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->value = val;
    n->next = 0;

    if (q->tail == 0) {
        q->head = n;
        q->tail = n;
        //@ close lseg(n, n, 0);
        //@ close queue(q, 1);
    } else {
        q->tail->next = n;
        //@ open queue(q, count);
        //@ assert lseg(q->head, q->tail, count - 1);
        //@ lseg_add(q->head, q->tail);
        q->tail = n;
        //@ close queue(q, count + 1);
    }
}