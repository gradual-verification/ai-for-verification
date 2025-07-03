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

lemma void lseg_append_node(struct node *from, struct node *middle)
    requires lseg(from, middle, ?c) &*& middle->value |-> ?v &*& middle->next |-> ?to &*& malloc_block_node(middle);
    ensures lseg(from, to, c + 1);
{
    open lseg(from, middle, c);
    if (from == middle) {
        close lseg(to, to, 0);
    } else {
        lseg_append_node(from->next, middle);
    }
    close lseg(from, to, c + 1);
}
@*/

// TODO: make this function pass the verification
void enqueue(struct queue *q, int val)
    //@ requires queue(q, ?count);
    //@ ensures queue(q, count + 1);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->value = val;
    n->next = 0;

    //@ open queue(q, count);
    struct node *old_tail = q->tail;
    if (old_tail == 0) {
        //@ assert count == 0;
        q->head = n;
        q->tail = n;
        //@ close lseg(n, n, 0);
    } else {
        //@ assert count > 0;
        old_tail->next = n;
        q->tail = n;
        //@ lseg_append_node(q->head, old_tail);
    }
    //@ close queue(q, count + 1);
}