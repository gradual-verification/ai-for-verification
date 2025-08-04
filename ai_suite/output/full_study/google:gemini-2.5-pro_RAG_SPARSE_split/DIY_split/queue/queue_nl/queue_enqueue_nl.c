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

predicate lseg(struct node *from, struct node *to, list<int> values) =
    from == to ?
        values == nil
    :
        from != 0 &*&
        from->next |-> ?next &*& from->value |-> ?val &*&
        malloc_block_node(from) &*&
        lseg(next, to, ?tail_values) &*&
        values == cons(val, tail_values);

predicate queue(struct queue *q, list<int> values) =
    q->head |-> ?h &*& q->tail |-> ?t &*& malloc_block_queue(q) &*&
    (
        values == nil ?
            h == 0 &*& t == 0
        :
            h != 0 &*& t != 0 &*&
            lseg(h, t, ?init_values) &*&
            t->next |-> 0 &*& t->value |-> ?last_val &*& malloc_block_node(t) &*&
            values == append(init_values, cons(last_val, nil))
    );

lemma void lseg_append_node(struct node *from, struct node *to)
    requires lseg(from, to, ?vs) &*&
             to != 0 &*& to->next |-> ?next &*& to->value |-> ?v &*& malloc_block_node(to);
    ensures lseg(from, next, append(vs, cons(v, nil)));
{
    open lseg(from, to, vs);
    if (from == to) {
        close lseg(next, next, nil);
        close lseg(to, next, cons(v, nil));
    } else {
        lseg_append_node(from->next, to);
        close lseg(from, next, append(vs, cons(v, nil)));
    }
}

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
    //@ requires queue(q, ?vs);
    //@ ensures queue(q, append(vs, cons(val, nil)));
{
    //@ open queue(q, vs);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->value = val;
    n->next = 0;

    if (q->tail == 0) {
        //@ assert vs == nil;
        q->head = n;
        q->tail = n;
        //@ close lseg(n, n, nil);
        //@ close queue(q, cons(val, nil));
    } else {
        //@ assert vs != nil;
        //@ struct node *old_tail = q->tail;
        q->tail->next = n;
        q->tail = n;
        //@ lseg_append_node(q->head, old_tail);
        //@ close queue(q, append(vs, cons(val, nil)));
    }
}