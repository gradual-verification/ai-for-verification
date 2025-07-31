
/*@

predicate lseg(void *first, void *last, list<void *> xs, predicate(void *) p) =
    first == last ?
        xs == nil
    :
    *((int*)first) |-> ?next &*& lseg((void*)next, last, ?xs0, p) &*& xs == cons(first, xs0) &*& p(first);

@*/


// TODO: make this function pass the verification
void lseg_remove(void *phead, void *element)
    //@ requires *((int*)phead) |-> ?head &*& lseg((void*)head, 0, ?xs, ?p) &*& mem(element, xs) == true;
    //@ ensures *((int*)phead) |-> ?head1 &*& lseg((void*)head1, 0, remove(element, xs), p) &*& *((int*)element) |-> _ &*& p(element);
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
