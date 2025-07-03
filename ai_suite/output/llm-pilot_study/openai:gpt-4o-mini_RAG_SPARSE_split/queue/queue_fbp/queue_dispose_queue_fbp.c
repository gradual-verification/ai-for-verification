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
predicate lseg(struct node *from, struct node *to, list<int> vs) =
    from == to ?
        vs == nil
    :
        from != 0 &*& from->value |-> ?v &*& from->next |-> ?next &*& malloc_block_node(from) &*& lseg(next, to, ?nvs) &*&
        vs == cons(v, nvs);

predicate queue(struct queue *q, list<int> vs) =
    q->head |-> ?head &*& q->tail |-> ?tail &*& malloc_block_queue(q) &*&
    (head == 0 ?
        tail == 0 &*& vs == nil
    :
        tail != 0 &*& lseg(head, tail, ?count) &*& tail->value |-> ?v &*& tail->next |-> 0 &*& vs == append(count, cons(v, nil)));
@*/

// TODO: make this function pass the verification
void dispose_queue(struct queue *q)
    //@ requires queue(q, ?vs);
    //@ ensures true;
{
    struct node *current = q->head;
    while (current != 0)
        //@ invariant lseg(current, 0, ?current_values) &*& append(current_values, vs) == vs;
    {
        struct node *next = current->next;
        free(current);
        current = next;
    }
    free(q);
}