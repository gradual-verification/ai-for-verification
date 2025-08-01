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

// TODO: make this function pass the verification
struct queue *create_queue()
    //@ requires true;
    //@ ensures queue(result, 0);
{
    struct queue *q = malloc(sizeof(struct queue));
    if (q == 0) abort();
    q->head = 0;
    q->tail = 0;
    return q;
}

// TODO: make this function pass the verification
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
    } else {
        q->tail->next = n;
        q->tail = n;
    }
}

// TODO: make this function pass the verification
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
        free(n);
    } else {
        val = n->value;
        struct node *next = n->next;
        q->head = next;
        free(n);
    }

    return val;
}

// TODO: make this function pass the verification
void dispose_queue(struct queue *q)
    //@ requires queue(q, 0);
    //@ ensures true;
{
    free(q);
}
