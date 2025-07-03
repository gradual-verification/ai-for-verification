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
predicate malloc_block_node(struct node *node) = malloc_block(node, sizeof(struct node));
predicate malloc_block_queue(struct queue *q) = malloc_block(q, sizeof(struct queue));

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

void dispose_queue(struct queue *q)
    //@ requires queue(q, 0);
    //@ ensures true;
{
    //@ open queue(q, 0);
    //@ open malloc_block_queue(q);
    //@ open integer_(&q->head, sizeof(void *), false, _);
    //@ integer__to_chars(&q->head, sizeof(void *), false);
    //@ open integer_(&q->tail, sizeof(void *), false, _);
    //@ integer__to_chars(&q->tail, sizeof(void *), false);
    //@ chars_join(q);
    //@ chars_to_chars_(q);
    free(q);
}