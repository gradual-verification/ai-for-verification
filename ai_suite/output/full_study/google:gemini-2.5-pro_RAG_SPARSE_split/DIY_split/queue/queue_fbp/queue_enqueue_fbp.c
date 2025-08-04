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

lemma void lseg_add(struct node *from, struct node *old_to)
    requires lseg(from, old_to, ?k) &*& old_to->value |-> ?v &*& old_to->next |-> ?new_to &*& malloc_block_node(old_to);
    ensures lseg(from, new_to, k + 1);
{
    open lseg(from, old_to, k);
    if (from == old_to) {
        close lseg(new_to, new_to, 0);
    } else {
        lseg_add(from->next, old_to);
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
    } else {
        //@ assert count > 0;
        //@ struct node *old_tail = q->tail;
        q->tail->next = n;
        q->tail = n;
        //@ lseg_add(q->head, old_tail);
    }
    //@ close queue(q, count + 1);
}