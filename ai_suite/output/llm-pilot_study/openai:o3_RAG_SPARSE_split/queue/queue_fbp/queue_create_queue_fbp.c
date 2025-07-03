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
        from->next  |-> ?next &*&
        malloc_block_node(from) &*&
        lseg(next, to, count - 1);

predicate queue(struct queue *q, int count) =
    q->head |-> ?head &*&
    q->tail |-> ?tail &*&
    malloc_block_queue(q) &*&
    (
      count == 0
        ? tail == 0                                // empty queue
        : count > 0 &*&                            // non-empty queue
          tail != 0 &*&
          lseg(head, tail, count - 1) &*&
          tail->value |-> ?v &*&
          tail->next  |-> 0 &*&
          malloc_block_node(tail)
    );
@*/

/* Creates an empty queue.                                    */
/* Verified to satisfy the contract `queue(result, 0)` exactly */
struct queue *create_queue()
    //@ requires true;
    //@ ensures  queue(result, 0);
{
    /* allocate the queue structure */
    struct queue *q = malloc(sizeof(struct queue));
    if (q == 0) abort();               /* malloc never returns 0 */

    /* initialise the fields */
    q->head = 0;
    q->tail = 0;

    /* At this point we own:
         - q->head |-> 0
         - q->tail |-> 0
         - malloc_block_queue(q)
       These are precisely the resources required by
       queue(q,0). */
    //@ close queue(q, 0);

    return q;
}