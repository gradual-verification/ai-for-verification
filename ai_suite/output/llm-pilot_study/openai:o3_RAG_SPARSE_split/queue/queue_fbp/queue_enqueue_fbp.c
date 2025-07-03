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
predicate lseg(struct node *from, struct node *to, int count) =
    from == to ?
        count == 0
    :
        count > 0 &*&
        from->value |-> ?v &*&
        from->next |-> ?next &*&
        malloc_block_node(from) &*&
        lseg(next, to, count - 1);

predicate queue(struct queue *q, int count) =
    q->head |-> ?head &*&
    q->tail |-> ?tail &*&
    malloc_block_queue(q) &*&
    (count == 0 ?
        tail == 0
    :
        count > 0 &*&
        tail != 0 &*&
        lseg(head, tail, count - 1) &*&
        tail->value |-> ?v &*&
        tail->next |-> 0 &*&
        malloc_block_node(tail));
@*/

/*@
lemma void lseg_extend_by_one(struct node *first)
    /* Extends list segment [first,to] with the node `to->next`                    */
    requires
        lseg(first, ?last, ?count) &*&
        last != 0 &*&
        last->value |-> ?v &*&
        last->next |-> ?new &*&
        malloc_block_node(last) &*&
        lseg(new, new, 0);                                    // new is the fresh tail
    ensures
        lseg(first, new, count + 1);
{
    open lseg(first, last, count);
    if (first == last) {
        /* base case: we are at the previous tail                            */
        open lseg(new, new, 0);        // consumes the empty segment on `new`
    } else {
        /* inductive step: move forward                                      */
        lseg_extend_by_one(first->next);
    }
    close lseg(first, new, _);          // rebuild segment with extended tail
}
@*/

// verified enqueue ------------------------------------------------------------
void enqueue(struct queue *q, int val)
    //@ requires queue(q, ?count);
    //@ ensures  queue(q, count + 1);
{
    /* allocate and initialise the new node                                   */
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->value = val;
    n->next  = 0;

    //@ open queue(q, count);

    if (q->tail == 0) {                       // --- empty queue --------------
        q->head = n;
        q->tail = n;

        //@ close lseg(n, n, 0);              // empty prefix
        //@ close queue(q, 1);                // list now contains one element
    } else {                                  // --- non-empty queue ----------
        struct node *old_tail = q->tail;

        /* we own the old tail’s fields via the queue predicate               */
        old_tail->next = n;                   // link new node
        q->tail        = n;                   // advance tail pointer

        //@ close lseg(n, n, 0);              // trivial segment for new tail
        //@ lseg_extend_by_one(q->head);       // extend main segment

        //@ close queue(q, count + 1);         // re-establish queue predicate
    }
}