#include "stdlib.h"

// Define the node structure
struct node {
    struct node *next;
    int value;
};

// Define the queue structure
struct queue {
    struct node *head;
    struct node *tail;
};

/*@
predicate nodes(struct node *n, list<int> values) =
    n == 0 ?
        values == nil
    :
        n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next, ?vs) &*& values == cons(v, vs);

predicate queue(struct queue *q, list<int> values) =
    q->head |-> ?head &*& q->tail |-> ?tail &*& malloc_block_queue(q) &*&
    nodes(head, values) &*& (values == nil ? head == tail : true) &*&
    (tail == 0 ? true : tail->next |-> 0);
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `enqueue` function puts a new node with the given value into the tail of a given queue. 
 *
 * @param q: the given queue to be enqueued
 * @param val: the given value to be added
 * 
 * The function makes sure that q has its number of elements incremented by 1. 
 */
void enqueue(struct queue *q, int val)
    //@ requires queue(q, ?values);
    //@ ensures queue(q, append(values, cons(val, nil)));
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->value = val;
    n->next = 0;

    //@ open queue(q, values);
    if (q->tail == 0) {
        q->head = n;
        q->tail = n;
        //@ close nodes(n, cons(val, nil));
    } else {
        //@ open nodes(q->tail, _);
        q->tail->next = n;
        q->tail = n;
        //@ close nodes(q->tail, cons(val, nil));
    }
    //@ close queue(q, append(values, cons(val, nil)));
}