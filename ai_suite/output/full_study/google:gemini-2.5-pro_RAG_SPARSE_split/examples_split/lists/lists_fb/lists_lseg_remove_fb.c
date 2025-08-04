#include "prelude.h"

/*@

predicate lseg(void *first, void *last, list<void *> xs, predicate(void *) p) =
    first == last ?
        xs == nil
    :
        first != 0 &*&
        *((void**)first) |-> ?next &*& lseg((void*)next, last, ?xs0, p) &*& xs == cons(first, xs0) &*& p(first);

lemma void lseg_snoc(void* first, void* last)
    requires lseg(first, last, ?xs, ?p) &*& p(last) &*& *((void**)last) |-> ?next;
    ensures lseg(first, next, snoc(xs, last), p);
{
    open lseg(first, last, xs, p);
    if (first == last) {
        close lseg(next, next, nil, p);
        close lseg(first, next, cons(first, nil), p);
    } else {
        lseg_snoc(*((void**)first), last);
        close lseg(first, next, snoc(xs, last), p);
    }
}

lemma void lseg_append(void* first, void* mid, void* last)
    requires lseg(first, mid, ?xs1, ?p) &*& lseg(mid, last, ?xs2, p);
    ensures lseg(first, last, append(xs1, xs2), p);
{
    open lseg(first, mid, xs1, p);
    if (first != mid) {
        lseg_append(*((void**)first), mid, last);
        close lseg(first, last, append(xs1, xs2), p);
    }
}

@*/


// TODO: make this function pass the verification
void lseg_remove(void *phead, void *element)
    //@ requires *((void**)phead) |-> ?head &*& lseg(head, 0, ?xs, ?p) &*& mem(element, xs) == true;
    //@ ensures *((void**)phead) |-> ?head1 &*& lseg(head1, 0, remove(element, xs), p) &*& *((void**)element) |-> _ &*& p(element);
{
    void **pnext = phead;
    //@ close lseg(*phead, *phead, nil, p);
    while (*pnext != element)
        /*@
        invariant
            *((void**)phead) |-> ?h &*&
            lseg(h, *pnext, ?prefix, p) &*&
            lseg(*pnext, 0, ?suffix, p) &*&
            xs == append(prefix, suffix) &*&
            mem(element, suffix) == true &*&
            *pnext != element;
        @*/
    {
        void* current_node = *pnext;
        //@ open lseg(current_node, 0, suffix, p);
        pnext = (void **)(current_node);
        //@ lseg_snoc(h, current_node);
        //@ append_assoc(prefix, cons(current_node, nil), tail(suffix));
    }
    
    //@ assert lseg(*((void**)phead), element, ?prefix, p);
    //@ assert lseg(element, 0, ?suffix, p);
    
    //@ open lseg(element, 0, suffix, p);
    void *nextNext = *((void **)element);
    *pnext = nextNext;
    
    //@ lseg_append(*((void**)phead), nextNext, 0);
    //@ assert remove(element, xs) == append(prefix, tail(suffix));
}