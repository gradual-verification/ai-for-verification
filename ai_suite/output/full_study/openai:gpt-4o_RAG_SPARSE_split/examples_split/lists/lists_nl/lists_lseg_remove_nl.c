#include <stdlib.h>

//@ #include "prelude.h"
//@ #include "list.gh"

// Define a predicate for a list segment
/*@
predicate lseg(void **phead, void *last, list<void *> vs) =
    phead == last ?
        vs == nil
    :
        pointer(phead, ?next) &*& lseg(next, last, ?vs0) &*& vs == cons(phead, vs0);
@*/

// TODO: make this function pass the verification
/* Description
    - Behavior: This function removes a specific element from the list segment starting from *phead*.
    - Parameters: *phead* is a pointer to the head of the list segment, *element* is the node that needs to be removed

It requires that element is part of the list segment starting from *phead*.
It ensures that the list segment doesn't have element anymore.
*/
void lseg_remove(void **phead, void *element)
    //@ requires lseg(phead, 0, ?vs) &*& mem(element, vs) == true;
    //@ ensures lseg(phead, 0, remove(element, vs));
{
    void **pnext = phead;
    while (*pnext != element)
        //@ invariant lseg(phead, pnext, ?vs1) &*& lseg(pnext, 0, ?vs2) &*& vs == append(vs1, vs2) &*& mem(element, vs2) == true;
    {
        //@ open lseg(pnext, 0, vs2);
        void **next = *pnext;
        pnext = next;
        //@ close lseg(phead, pnext, vs1);
    }
    {
        //@ open lseg(pnext, 0, vs2);
        void *nextNext = *((void **)*pnext);
        *pnext = nextNext;
        //@ close lseg(phead, pnext, vs1);
        //@ close lseg(pnext, 0, remove(element, vs2));
    }
    //@ close lseg(phead, 0, remove(element, vs));
}