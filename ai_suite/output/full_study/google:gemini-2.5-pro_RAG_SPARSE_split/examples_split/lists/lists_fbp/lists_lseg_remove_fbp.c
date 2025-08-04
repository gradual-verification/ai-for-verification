/*@

predicate lseg(void *first, void *last, list<void *> xs, predicate(void *) p) =
    first == last ?
        xs == nil
    :
        pointer(first, ?next) &*& lseg(next, last, ?xs0, p) &*& xs == cons(first, xs0) &*& p(first);

predicate lseg_prefix(void **p_p_start, void **p_p_end, list<void *> prefix, predicate(void *) p) =
    p_p_start == p_p_end ?
        prefix == nil
    :
        pointer(p_p_start, ?h) &*& h != 0 &*& p(h) &*& prefix == cons(h, ?rest_prefix) &*&
        lseg_prefix((void **)h, p_p_end, rest_prefix, p);

lemma void lseg_prefix_append_node(void **p_p_start, void **p_p_mid)
    requires lseg_prefix(p_p_start, p_p_mid, ?prefix, ?p) &*& pointer(p_p_mid, ?h) &*& p(h);
    ensures lseg_prefix(p_p_start, (void **)h, append(prefix, cons(h, nil)), p);
{
    open lseg_prefix(p_p_start, p_p_mid, prefix, p);
    if (p_p_start != p_p_mid) {
        lseg_prefix_append_node((void **)*p_p_start, p_p_mid);
    }
    close lseg_prefix(p_p_start, (void **)h, append(prefix, cons(h, nil)), p);
}

lemma void lseg_prefix_rejoin(void **p_p_start, void **p_p_end)
    requires lseg_prefix(p_p_start, p_p_end, ?prefix, ?p) &*& pointer(p_p_end, ?end_node) &*& lseg(end_node, 0, ?suffix, p);
    ensures lseg(*p_p_start, 0, append(prefix, suffix), p) &*& pointer(p_p_start, _);
{
    open lseg_prefix(p_p_start, p_p_end, prefix, p);
    if (p_p_start == p_p_end) {
        // prefix is nil.
    } else {
        lseg_prefix_rejoin((void **)*p_p_start, p_p_end);
        close lseg(*p_p_start, 0, append(prefix, suffix), p);
    }
}

lemma void remove_append_prefix(list<void*> prefix, list<void*> suffix, void* element)
    requires head(suffix) == element &*& !mem(element, prefix);
    ensures remove(element, append(prefix, suffix)) == append(prefix, tail(suffix));
{
    switch(prefix) {
        case nil:
        case cons(h, t):
            remove_append_prefix(t, suffix, element);
    }
}

@*/


// TODO: make this function pass the verification
void lseg_remove(void *phead, void *element)
    //@ requires pointer(phead, ?head) &*& lseg(head, 0, ?xs, ?p) &*& mem(element, xs) == true;
    //@ ensures pointer(phead, ?head1) &*& lseg(head1, 0, remove(element, xs), p) &*& pointer(element, _) &*& p(element);
{
    void **pnext = phead;
    //@ close lseg_prefix(phead, phead, nil, p);

    while (*pnext != element)
        /*@
        invariant
            lseg_prefix(phead, pnext, ?xs_prefix, p) &*&
            pointer(pnext, ?curr) &*& lseg(curr, 0, ?xs_suffix, p) &*&
            xs == append(xs_prefix, xs_suffix) &*&
            mem(element, xs_suffix) == true &*&
            !mem(element, xs_prefix);
        @*/
    {
        //@ open lseg(*pnext, 0, xs_suffix, p);
        //@ lseg_prefix_append_node(phead, pnext);
        void *current_node = *pnext;
        pnext = (void **)current_node;
    }

    //@ assert lseg_prefix(phead, pnext, ?xs_prefix, p);
    //@ assert pointer(pnext, element);
    //@ assert lseg(element, 0, ?xs_suffix, p);
    //@ assert xs == append(xs_prefix, xs_suffix);
    //@ assert head(xs_suffix) == element;
    //@ assert !mem(element, xs_prefix);

    //@ open lseg(element, 0, xs_suffix, p);
    //@ assert pointer(element, ?nextNext) &*& lseg(nextNext, 0, tail(xs_suffix), p) &*& p(element);

    {
        void *nextNext_val = *((void **)*pnext);
        *pnext = nextNext_val;
    }

    //@ assert pointer(pnext, nextNext);
    //@ lseg_prefix_rejoin(phead, pnext);
    //@ assert lseg(?head1, 0, append(xs_prefix, tail(xs_suffix)), p) &*& pointer(phead, head1);

    //@ remove_append_prefix(xs_prefix, xs_suffix, element);
}