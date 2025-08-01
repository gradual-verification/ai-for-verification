
/*@

predicate lseg(void *first, void *last, list<void *> xs, predicate(void *) p) =
    first == last ?
        xs == nil
    :
        pointer(first, ?next) &*& lseg(next, last, ?xs0, p) &*& xs == cons(first, xs0) &*& p(first);

@*/


// TODO: make this function pass the verification
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
