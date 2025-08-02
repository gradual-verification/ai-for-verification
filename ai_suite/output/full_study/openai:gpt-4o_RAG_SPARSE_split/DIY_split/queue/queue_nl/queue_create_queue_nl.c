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
predicate nodes(struct node *node, list<int> values) =
    node == 0 ?
        values == nil
    :
        node->next |-> ?next &*& node->value |-> ?value &*& malloc_block_node(node) &*&
        nodes(next, ?values0) &*& values == cons(value, values0);

predicate queue(struct queue *q, list<int> values) =
    q->head |-> ?head &*& q->tail |-> ?tail &*& malloc_block_queue(q) &*&
    nodes(head, values) &*& (values == nil ? head == 0 &*& tail == 0 : tail != 0);
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `create_queue` function creates an empty heap. 
 *
 * The function makes sure that the returned heap has no element. 
 */
//@ requires true;
//@ ensures result != 0 ? queue(result, nil) : true;
struct queue *create_queue()
{
    struct queue *q = malloc(sizeof(struct queue));
    if (q == 0) abort();
    q->head = 0;
    q->tail = 0;
    //@ close nodes(0, nil);
    //@ close queue(q, nil);
    return q;
}