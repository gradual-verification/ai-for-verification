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

// A list segment from `from` (inclusive) to `to` (exclusive).
predicate lseg(struct node *from, struct node *to, list<int> values) =
    from == to ?
        values == nil
    :
        from != 0 &*&
        from->next |-> ?next &*& from->value |-> ?val &*& malloc_block_node(from) &*&
        lseg(next, to, ?tail_values) &*&
        values == cons(val, tail_values);

// A queue is a list segment from `head` to `tail`, plus the `tail` node itself.
// `tail->next` is null. An empty queue has null head and tail.
predicate queue(struct queue *q; list<int> values) =
    q->head |-> ?h &*& q->tail |-> ?t &*& malloc_block_queue(q) &*&
    (
        h == 0 ?
            // Empty queue
            t == 0 &*& values == nil
        :
            // Non-empty queue
            lseg(h, t, ?prefix_values) &*&
            t->next |-> 0 &*& t->value |-> ?last_val &*& malloc_block_node(t) &*&
            values == append(prefix_values, cons(last_val, nil))
    );

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
int dequeue(struct queue *q)
    //@ requires [?f]queue(q, ?vs) &*& vs != nil;
    //@ ensures [f]queue(q, tail(vs)) &*& result == head(vs);
{
    //@ open queue(q, vs);
    // From `vs != nil`, we know `h != 0` and are in the non-empty case of the predicate.
    // We have: q->head |-> ?h, q->tail |-> ?t, malloc_block_queue(q)
    // &*& lseg(h, t, ?p_vs) &*& t->next |-> 0 &*& t->value |-> ?l_val &*& malloc_block_node(t)
    // &*& vs == append(p_vs, cons(l_val, nil));
    struct node *n = q->head;
    int val;

    if (q->head == q->tail) {
        // This is the single-element case. `h == t`, so `lseg(h, h, p_vs)` implies `p_vs == nil`.
        // Therefore, `vs == cons(l_val, nil)`.
        // `head(vs)` is `l_val` and `tail(vs)` is `nil`.
        //@ open lseg(n, q->tail, p_vs);
        val = q->tail->value;
        q->head = 0;
        q->tail = 0;
        free(n);
        //@ close [f]queue(q, nil);
    } else {
        // This is the multi-element case. `h != t`, so `p_vs != nil`.
        // `vs == append(p_vs, cons(l_val, nil))`.
        // `head(vs) == head(p_vs)`.
        // `tail(vs) == append(tail(p_vs), cons(l_val, nil))`.
        //@ open lseg(n, q->tail, p_vs);
        // `p_vs` is `cons(?n_val, ?p_vs_tail)`. `head(vs)` is `n_val`.
        val = n->value;
        struct node *next = n->next;
        q->head = next;
        free(n);
        // The new queue state has head `next`, tail `t`, and values `append(p_vs_tail, cons(l_val, nil))`.
        // This corresponds to `tail(vs)`.
        //@ close [f]queue(q, append(tail(p_vs), cons(l_val, nil)));
    }

    return val;
}