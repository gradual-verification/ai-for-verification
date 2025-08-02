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
predicate nodes(struct node *node; list<int> values) =
    node == 0 ?
        values == nil
    :
        node->next |-> ?next &*& node->value |-> ?value &*& malloc_block_node(node) &*&
        nodes(next, ?values0) &*& values == cons(value, values0);

predicate queue(struct queue *q; list<int> values) =
    q->head |-> ?head &*& q->tail |-> ?tail &*& malloc_block_queue(q) &*&
    nodes(head, values) &*& (values == nil ? head == tail : true);
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
/*@
requires queue(q, nil);
ensures emp;
@*/
void dispose_queue(struct queue *q)
{
    //@ open queue(q, nil);
    //@ open nodes(q->head, nil);
    free(q);
}