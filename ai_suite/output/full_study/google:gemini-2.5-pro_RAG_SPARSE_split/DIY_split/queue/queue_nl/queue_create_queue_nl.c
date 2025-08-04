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

// A predicate representing a list segment from 'from' (inclusive) to 'to' (exclusive).
// 'values' is the list of integer values in the segment's nodes.
predicate lseg(struct node *from, struct node *to, list<int> values) =
    from == to ?
        values == nil
    :
        from != 0 &*&
        from->next |-> ?next &*&
        from->value |-> ?value &*&
        malloc_block_node(from) &*&
        lseg(next, to, ?rest) &*&
        values == cons(value, rest);

// A predicate representing a queue and its contents as a list of values.
predicate queue(struct queue *q, list<int> values) =
    q->head |-> ?h &*& q->tail |-> ?t &*& malloc_block_queue(q) &*&
    (
        h == 0 ?
            // Case 1: The queue is empty.
            t == 0 &*& values == nil
        :
            // Case 2: The queue is not empty.
            h != 0 &*& t != 0 &*&
            lseg(h, t, ?prefix_values) &*&
            t->next |-> 0 &*& t->value |-> ?last_value &*& malloc_block_node(t) &*&
            values == append(prefix_values, cons(last_value, nil))
    );

@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `create_queue` function creates an empty heap. 
 *
 * The function makes sure that the returned heap has no element. 
 */
struct queue *create_queue()
    //@ requires true;
    //@ ensures queue(result, nil);
{
    struct queue *q = malloc(sizeof(struct queue));
    if (q == 0) abort();
    q->head = 0;
    q->tail = 0;
    //@ close queue(q, nil);
    return q;
}