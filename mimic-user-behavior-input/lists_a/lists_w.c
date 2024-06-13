#include "stdlib.h"
#include "bool.h"
#include "lists.h"

void lseg_remove(void *phead, void *element)
    //@ requires pointer(phead, ?head) &*& lseg(head, 0, ?xs, ?p) &*& mem(element, xs) == true;
    //@ ensures pointer(phead, ?head1) &*& lseg(head1, 0, remove(element, xs), p) &*& pointer(element, _) &*& p(element);
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
