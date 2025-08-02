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
// Define a predicate for a linked list of nodes
predicate nodes(struct node *n; list<int> values) =
    n == 0 ?
        values == nil
    :
        n->next |-> ?next &*& n->value |-> ?value &*& malloc_block_node(n) &*&
        nodes(next, ?values0) &*&
        values == cons(value, values0);

// Define a predicate for an empty queue
predicate empty_queue(struct queue *q) =
    q->head |-> 0 &*& q->tail |-> 0 &*& malloc_block_queue(q);

// Define a predicate for a queue with contents
predicate queue(struct queue *q; list<int> values) =
    q->head |-> ?head &*& q->tail |-> ?tail &*& malloc_block_queue(q) &*&
    head == 0 ?
        values == nil &*& tail == 0
    :
        nodes(head, values) &*& tail != 0;
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `dispose_queue` function frees an empty queue. 
 *
 * @param q: the given empty queue to be freed
 * 
 * It makes sure that q is freed. 
 */
void dispose_queue(struct queue *q)
    //@ requires queue(q, nil);
    //@ ensures true;
{
    //@ open queue(q, nil);
    //@ assert q->head |-> 0;
    //@ assert q->tail |-> 0;
    free(q);
}