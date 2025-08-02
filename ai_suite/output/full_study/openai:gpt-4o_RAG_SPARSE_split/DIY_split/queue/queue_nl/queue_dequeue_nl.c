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
    nodes(head, ?nodes_values) &*&
    (nodes_values == nil ? head == tail : true) &*&
    (nodes_values != nil ? mem(tail, nodes_values) == true : true) &*&
    values == nodes_values;
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `dequeue` function removes the head of a non-empty heap and returns its value. 
 *
 * @param q: the given non-empty queue to be dequeued
 * 
 * This function makes sure that q has its number of elements decremented by 1. 
 */
/*@
requires queue(q, ?values) &*& values != nil;
ensures queue(q, ?new_values) &*& values == cons(result, new_values);
@*/
int dequeue(struct queue *q)
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