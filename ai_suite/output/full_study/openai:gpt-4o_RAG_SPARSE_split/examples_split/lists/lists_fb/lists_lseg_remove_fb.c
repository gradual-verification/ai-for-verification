#include "stdlib.h"

/*@

predicate lseg(void *first, void *last, list<void *> xs, predicate(void *) p) =
    first == last ?
        xs == nil
    :
    *((int*)first) |-> ?next &*& lseg((void*)next, last, ?xs0, p) &*& xs == cons(first, xs0) &*& p(first);

@*/

// Lemma to split a linked segment at a given node
lemma void lseg_split(void *first, void *node, void *last, list<void *> xs, predicate(void *) p)
    requires lseg(first, last, xs, p) &*& mem(node, xs) == true;
    ensures lseg(first, node, ?xs1, p) &*& lseg(node, last, ?xs2, p) &*& xs == append(xs1, xs2) &*& mem(node, xs1) == false;
{
    open lseg(first, last, xs, p);
    if (first != last) {
        if (first == node) {
            close lseg(first, node, nil, p);
            close lseg(node, last, xs, p);
        } else {
            lseg_split((void *)*((int *)first), node, last, ?xs0, p);
            close lseg(first, node, cons(first, xs0), p);
        }
    }
}

// Lemma to merge two linked segments
lemma void lseg_merge(void *first, void *node, void *last, list<void *> xs1, list<void *> xs2, predicate(void *) p)
    requires lseg(first, node, xs1, p) &*& lseg(node, last, xs2, p);
    ensures lseg(first, last, append(xs1, xs2), p);
{
    open lseg(first, node, xs1, p);
    if (first != node) {
        lseg_merge((void *)*((int *)first), node, last, ?xs10, xs2, p);
        close lseg(first, last, cons(first, append(xs10, xs2)), p);
    }
}

// TODO: make this function pass the verification
void lseg_remove(void *phead, void *element)
    //@ requires *((int*)phead) |-> ?head &*& lseg((void*)head, 0, ?xs, ?p) &*& mem(element, xs) == true;
    //@ ensures *((int*)phead) |-> ?head1 &*& lseg((void*)head1, 0, remove(element, xs), p) &*& *((int*)element) |-> _ &*& p(element);
{
    void **pnext = phead;
    while (*pnext != element)
    //@ invariant *((int*)phead) |-> ?head0 &*& lseg((void*)head0, *pnext, ?xs0, p) &*& lseg(*pnext, 0, ?xs1, p) &*& xs == append(xs0, xs1) &*& mem(element, xs1) == true;
    {
        //@ open lseg(*pnext, 0, xs1, p);
        void **next = *pnext;
        pnext = next;
        //@ close lseg(*pnext, 0, xs1, p);
    }
    {
        //@ open lseg(*pnext, 0, xs1, p);
        void *nextNext = *((void **)*pnext);
        *pnext = nextNext;
        //@ close lseg(*pnext, 0, xs1, p);
    }
    //@ lseg_merge((void*)head0, *pnext, 0, xs0, tail(xs1), p);
}