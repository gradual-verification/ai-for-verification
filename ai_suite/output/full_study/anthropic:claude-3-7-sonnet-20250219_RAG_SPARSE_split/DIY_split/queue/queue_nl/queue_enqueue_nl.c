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
// Define a predicate for a linked list segment from 'first' to 'last'
predicate nodes(struct node *first, struct node *last; list<int> values) =
    first == last ?
        values == nil
    :
        first != 0 &*& first->next |-> ?next &*& first->value |-> ?value &*&
        malloc_block_node(first) &*& nodes(next, last, ?tail_values) &*&
        values == cons(value, tail_values);

// Define a predicate for the queue structure
predicate queue(struct queue *q; list<int> values) =
    q->head |-> ?head &*& q->tail |-> ?tail &*&
    malloc_block_queue(q) &*&
    head != 0 &*& tail != 0 &*&
    nodes(head, tail, values) &*&
    tail->next |-> 0 &*& tail->value |-> _;
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
        //@ assert q->head |-> ?head;
        //@ assert q->tail |-> 0;
        q->head = n;
        q->tail = n;
        //@ close nodes(n, n, nil);
        //@ close queue(q, cons(val, nil));
    } else {
        //@ assert q->head |-> ?head;
        //@ assert q->tail |-> ?tail;
        //@ assert tail->next |-> 0;
        //@ assert nodes(head, tail, values);
        
        q->tail->next = n;
        q->tail = n;
        
        /*@
        // We need to prove that appending a value to the queue is equivalent to
        // extending the nodes predicate
        lemma void append_nodes_lemma(struct node *first, struct node *last, struct node *new_last)
            requires nodes(first, last, ?vs) &*& last->next |-> new_last &*& 
                     new_last != 0 &*& new_last->value |-> ?val &*& 
                     new_last->next |-> 0 &*& malloc_block_node(new_last);
            ensures nodes(first, new_last, append(vs, cons(val, nil)));
        {
            open nodes(first, last, vs);
            if (first == last) {
                close nodes(new_last, new_last, nil);
                close nodes(first, new_last, cons(first->value, nil));
            } else {
                append_nodes_lemma(first->next, last, new_last);
                close nodes(first, new_last, append(vs, cons(val, nil)));
            }
        }
        @*/
        
        //@ append_nodes_lemma(head, tail, n);
        //@ close queue(q, append(values, cons(val, nil)));
    }
}