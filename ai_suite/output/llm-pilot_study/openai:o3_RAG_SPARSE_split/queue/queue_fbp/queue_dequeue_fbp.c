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
        count > 0 &*& from->value |-> ?v &*& from->next |-> ?next &*&
        malloc_block_node(from) &*& lseg(next, to, count - 1);

predicate queue(struct queue *q, int count) =
    q->head |-> ?head &*& q->tail |-> ?tail &*& malloc_block_queue(q) &*&
    (count == 0 ?
        tail == 0 &*& head == 0 &*& lseg(head, tail, 0)
     :
        tail != 0 &*& lseg(head, tail, count - 1) &*&
        tail->value |-> ?v_tail &*& tail->next |-> 0 &*& malloc_block_node(tail));
@*/

/* ---------------------------------------------------------------- */
/*  dequeue                                                         */
/* ---------------------------------------------------------------- */

/*@
lemma void lseg_nonempty(struct node *h, struct node *t, int c)
    requires lseg(h, t, c) &*& c > 0;
    ensures h != t;
{
    open lseg(h, t, c);
    if (h == t) {
        open lseg(t, t, _); /* contradiction: c>0 implies h!=t            */
    }
    close lseg(h, t, c);
}
@*/

// The verified dequeue function
int dequeue(struct queue *q)
    //@ requires queue(q, ?count) &*& count > 0;
    //@ ensures  queue(q, count - 1);
{
    //@ open queue(q, count);
    struct node *n   = q->head;
    struct node *tail = q->tail;
    int val;

    if (n == tail) /* the queue contains exactly one element */
    {
        //@   open lseg(n, tail, count - 1);          /* count - 1 == 0 */
        //@   assert count == 1;                      /* because h==t   */
        val = n->value;

        q->head = 0;
        q->tail = 0;

        //@   close lseg(0, 0, 0);                   /* empty list     */
        //@   close queue(q, 0);
        free(n);                                    /* safe: we own   */
    }
    else           /* at least two elements */
    {
        //@   lseg_nonempty(n, tail, count - 1);     /* h != t already */
        //@   open lseg(n, tail, count - 1);         /* expose first   */

        val              = n->value;
        struct node *next = n->next;
        q->head          = next;

        /* the remainder of the list is still described by
           lseg(next, tail, count-2) obtained from the open above. */
        //@   close lseg(next, tail, count - 2);     /* restore chunk  */
        free(n);                                    /* free first node*/

        //@   close queue(q, count - 1);
    }
    return val;
}