#include "stdlib.h"
#include <stdbool.h>

/*@

predicate lseg(void *first, void *last, list<void *> xs, predicate(void *) p) =
    first == last ?
        xs == nil
    :
    *first |-> ?next &*& lseg(next, last, ?xs0, p) &*& xs == cons(first, xs0) &*& p(first);

@*/

void lseg_remove(void *phead, void *element)
    //@ requires *phead |-> ?head &*& lseg(head, 0, ?xs, ?p) &*& mem(element, xs) == true;
    //@ ensures *phead |-> ?head1 &*& lseg(head1, 0, remove(element, xs), p) &*& *element |-> _ &*& p(element);
{
    void **pnext = phead;
    while (*pnext != element)
    {
        void **next = *pnext;
        pnext = next;
    }
    {
        void *nextNext = *((void **)*pnext);
        *pnext = nextNext;
    }
}
