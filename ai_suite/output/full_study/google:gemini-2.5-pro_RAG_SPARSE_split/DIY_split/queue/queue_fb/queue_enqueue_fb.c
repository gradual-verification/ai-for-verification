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

lemma void lseg_append(struct node *from, struct node *to)
    requires lseg(from, to, ?k) &*& to->value |-> ?v &*& to->next |-> ?new_to;
    ensures lseg(from, new_to, k + 1);
{
    open lseg(from, to, k);
    if (from == to) {
        close lseg(new_to, new_to, 0);
    } else {
        lseg_append(from->next, to);
    }
    close lseg(from, new_to, k + 1);
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
    if (q->tail == 0) {
        //@ assert count == 0;
        q->head = n;
        q->tail = n;
        //@ close lseg(n, n, 0);
        //@ close queue(q, count + 1);
    } else {
        //@ assert count > 0;
        //@ assert q->head |-> ?head &*& q->tail |-> ?old_tail;
        q->tail->next = n;
        //@ lseg_append(head, old_tail);
        q->tail = n;
        //@ close queue(q, count + 1);
    }
}