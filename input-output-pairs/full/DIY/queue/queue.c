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

/*@
lemma void lseg_add(struct node *head, struct node *tail, struct node *new_tail, int count)
    requires lseg(head, tail, count) &*& tail->value |-> ?v1 &*& tail->next |-> new_tail &*& new_tail->value |-> ?v2 &*& malloc_block_node(tail);
    ensures lseg(head, new_tail, count + 1) &*& new_tail->value |-> v2;
{
    if (head == tail) {
        open lseg(head, tail, count);
        close lseg(new_tail, new_tail, 0);
        close lseg(head, new_tail, 1);
    } else {
        open lseg(head, tail, count);
        struct node *next = head->next;
        lseg_add(next, tail, new_tail, count - 1);
        close lseg(head, new_tail, count + 1);
    }
}
@*/

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

void enqueue(struct queue *q, int val)
    //@ requires queue(q, ?count);
    //@ ensures queue(q, count + 1);
{
    //@ open queue(q, count);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->value = val;
    n->next = 0;

    if (q->tail == 0) {
        q->head = n;
        q->tail = n;
        //@ close lseg(q->head, q->tail, 0);
        //@ close queue(q, 1);
    } else {
        q->tail->next = n;
        //@ lseg_add(q->head, q->tail, n, count - 1);
        q->tail = n;
        //@ close queue(q, count + 1);
    }
}

int dequeue(struct queue *q)
    //@ requires queue(q, ?count) &*& count > 0;
    //@ ensures queue(q, count - 1);
{
    //@ open queue(q, count);
    //@ open lseg(q->head, q->tail, count - 1);
    struct node *n = q->head;
    int val;

    if (q->head == q->tail) {
        val = q->tail->value;
        q->head = 0;
        q->tail = 0;
        free(n);
        //@ close queue(q, 0);
    } else {
        val = n->value;
        struct node *next = n->next;
        q->head = next;
        free(n);
        //@ close queue(q, count - 1);
    }

    return 1;
}

void dispose_queue(struct queue *q)
    //@ requires queue(q, 0);
    //@ ensures true;
{
    //@ open queue(q, 0);
    free(q);
}
