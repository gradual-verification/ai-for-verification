/*@

predicate lseg(void *first, void *last, list<void *> xs, predicate(void *) p) =
    first == last ?
        xs == nil
    :
        pointer(first, ?next) &*& lseg(next, last, ?xs0, p) &*& xs == cons(first, xs0) &*& p(first);

@*/


void lseg_remove(void *phead, void *element)
    //@ requires pointer(phead, ?head) &*& lseg(head, 0, ?xs, ?p) &*& mem(element, xs) == true;
    //@ ensures pointer(phead, ?head1) &*& lseg(head1, 0, remove(element, xs), p) &*& pointer(element, _) &*& p(element);
{
    void **pnext = phead;
    //@ open lseg(head, 0, xs, p);
    //@ if (head == element) {
    //@     assert pointer(head, ?next);
    //@     assert lseg(next, 0, ?xs0, p);
    //@     assert xs == cons(head, xs0);
    //@     assert p(head);
    //@     *pnext = next;
    //@     close pointer(element, next);
    //@     close pointer(phead, next);
    //@     close lseg(next, 0, xs0, p);
    //@     assert remove(element, xs) == xs0;
    //@ } else {
    while (*pnext != element)
    //@ invariant pointer(pnext, ?current) &*& lseg(current, 0, ?remaining, p) &*& mem(element, remaining) == true &*& 
    //@           lseg(head, current, ?prefix, p) &*& xs == append(prefix, remaining) &*& 
    //@           remove(element, xs) == append(prefix, remove(element, remaining));
    {
        void **next = *pnext;
        //@ open lseg(current, 0, remaining, p);
        //@ assert pointer(current, ?next_node);
        //@ assert lseg(next_node, 0, ?rest, p);
        //@ assert remaining == cons(current, rest);
        //@ assert p(current);
        //@ close lseg(current, next_node, cons(current, nil), p);
        //@ assert lseg(head, current, prefix, p);
        //@ assert lseg(current, next_node, cons(current, nil), p);
        //@ lseg_join(head, current, next_node);
        //@ assert lseg(head, next_node, append(prefix, cons(current, nil)), p);
        //@ assert mem(element, rest) == true;
        //@ assert remove(element, remaining) == cons(current, remove(element, rest));
        //@ assert remove(element, xs) == append(prefix, remove(element, remaining));
        //@ assert remove(element, remaining) == cons(current, remove(element, rest));
        //@ assert remove(element, xs) == append(prefix, cons(current, remove(element, rest)));
        //@ assert append(prefix, cons(current, remove(element, rest))) == append(append(prefix, cons(current, nil)), remove(element, rest));
        //@ append_assoc(prefix, cons(current, nil), remove(element, rest));
        //@ assert remove(element, xs) == append(append(prefix, cons(current, nil)), remove(element, rest));
        pnext = next;
    }
    //@ open lseg(current, 0, remaining, p);
    //@ assert pointer(current, ?next_node);
    //@ assert lseg(next_node, 0, ?rest, p);
    //@ assert remaining == cons(current, rest);
    //@ assert p(current);
    //@ assert current == element;
    {
        void *nextNext = *((void **)*pnext);
        //@ assert nextNext == next_node;
        *pnext = nextNext;
        //@ close pointer(element, next_node);
        //@ assert lseg(next_node, 0, rest, p);
        //@ assert remove(element, remaining) == rest;
        //@ assert remove(element, xs) == append(prefix, remove(element, remaining));
        //@ assert remove(element, xs) == append(prefix, rest);
        //@ assert lseg(head, element, prefix, p);
        //@ lseg_join(head, element, 0);
        //@ assert lseg(head, 0, append(prefix, rest), p);
        //@ assert append(prefix, rest) == remove(element, xs);
    }
    //@ }
}