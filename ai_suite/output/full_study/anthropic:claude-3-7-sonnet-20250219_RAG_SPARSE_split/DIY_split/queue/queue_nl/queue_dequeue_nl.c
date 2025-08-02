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
// Define a predicate for a linked list segment
predicate lseg(struct node *first, struct node *last, struct node *next_after_last; list<int> values) =
    first == last ?
        next_after_last == last->next &*& last->value |-> ?v &*& values == cons(v, nil)
    :
        first != 0 &*& first->next |-> ?next &*& first->value |-> ?v &*&
        malloc_block_node(first) &*& lseg(next, last, next_after_last, ?tail_values) &*&
        values == cons(v, tail_values);

// Define a predicate for an empty queue
predicate empty_queue(struct queue *q) =
    q->head |-> 0 &*& q->tail |-> 0 &*& malloc_block_queue(q);

// Define a predicate for a non-empty queue
predicate non_empty_queue(struct queue *q, list<int> values) =
    q->head |-> ?head &*& q->tail |-> ?tail &*& 
    head != 0 &*& tail != 0 &*&
    malloc_block_queue(q) &*&
    (head == tail ?
        head->next |-> 0 &*& head->value |-> ?v &*& malloc_block_node(head) &*& values == cons(v, nil)
    :
        lseg(head, tail, 0, values) &*& tail->next |-> 0);

// Define a general queue predicate
predicate queue(struct queue *q, list<int> values) =
    values == nil ?
        empty_queue(q)
    :
        non_empty_queue(q, values);
@*/

/***
 * Description:
 * The `dequeue` function removes the head of a non-empty heap and returns its value. 
 *
 * @param q: the given non-empty queue to be dequeued
 * 
 * This function makes sure that q has its number of elements decremented by 1. 
 */
int dequeue(struct queue *q)
//@ requires queue(q, ?values) &*& values != nil;
//@ ensures queue(q, tail(values)) &*& result == head(values);
{
    struct node *n = q->head;
    int val;

    if (q->head == q->tail) {
        //@ open queue(q, values);
        //@ open non_empty_queue(q, values);
        val = q->tail->value;
        q->head = 0;
        q->tail = 0;
        free(n);
        //@ close empty_queue(q);
        //@ close queue(q, nil);
    } else {
        //@ open queue(q, values);
        //@ open non_empty_queue(q, values);
        //@ open lseg(n, q->tail, 0, values);
        val = n->value;
        struct node *next = n->next;
        q->head = next;
        free(n);
        //@ close non_empty_queue(q, tail(values));
        //@ close queue(q, tail(values));
    }

    return val;
}