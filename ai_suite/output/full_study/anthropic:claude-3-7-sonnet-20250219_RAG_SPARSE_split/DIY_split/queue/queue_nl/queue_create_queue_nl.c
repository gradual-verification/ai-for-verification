#include "stdlib.h"

/*@
// Define a predicate for a linked list of nodes
predicate nodes(struct node *n; list<int> values) =
    n == 0 ?
        values == nil
    :
        n->next |-> ?next &*& n->value |-> ?value &*& malloc_block_node(n) &*&
        nodes(next, ?values0) &*& values == cons(value, values0);

// Define a predicate for the queue structure
predicate queue(struct queue *q; list<int> values) =
    q->head |-> ?head &*& q->tail |-> ?tail &*&
    malloc_block_queue(q) &*&
    (head == 0 ?
        values == nil &*& tail == 0
    :
        nodes(head, values) &*& tail == 0 ? true : mem(tail, values) == true);
@*/

struct node {
    struct node *next;
    int value;
};

struct queue {
    struct node *head;
    struct node *tail;
};

// TODO: make this function pass the verification
/***
 * Description:
 * The `create_queue` function creates an empty heap. 
 *
 * The function makes sure that the returned heap has no element. 
 */
struct queue *create_queue()
//@ requires true;
//@ ensures result == 0 ? true : queue(result, nil);
{
    struct queue *q = malloc(sizeof(struct queue));
    //@ if (q == 0) return 0;
    if (q == 0) abort();
    q->head = 0;
    q->tail = 0;
    //@ close nodes(0, nil);
    //@ close queue(q, nil);
    return q;
}