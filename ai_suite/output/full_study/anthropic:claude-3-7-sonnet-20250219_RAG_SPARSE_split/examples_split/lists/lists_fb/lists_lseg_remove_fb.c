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
    /*@
    // Define a lemma to split a list segment at a specific element
    lemma void lseg_split(void *from, void *to, void *element, list<void *> xs, predicate(void *) p)
        requires lseg(from, to, xs, p) &*& mem(element, xs) == true;
        ensures lseg(from, element, ?xs1, p) &*& *((int*)element) |-> ?next &*& lseg((void*)next, to, ?xs2, p) &*& 
                xs == append(xs1, cons(element, xs2)) &*& p(element);
    {
        open lseg(from, to, xs, p);
        if (from == to) {
            // This case is impossible because mem(element, nil) is false
        } else {
            if (from == element) {
                close lseg(from, element, nil, p);
            } else {
                lseg_split((void*)*((int*)from), to, element, xs0, p);
                close lseg(from, element, cons(from, xs1), p);
            }
        }
    }
    
    // Define a lemma to merge two list segments
    lemma void lseg_merge(void *from, void *mid, void *to, list<void *> xs1, list<void *> xs2, predicate(void *) p)
        requires lseg(from, mid, xs1, p) &*& lseg(mid, to, xs2, p);
        ensures lseg(from, to, append(xs1, xs2), p);
    {
        open lseg(from, mid, xs1, p);
        if (from == mid) {
            // Base case: first segment is empty
        } else {
            lseg_merge((void*)*((int*)from), mid, to, tail(xs1), xs2, p);
            close lseg(from, to, append(xs1, xs2), p);
        }
    }
    @*/
    
    void **pnext = phead;
    while (*pnext != element)
        /*@
        invariant *pnext |-> ?current &*& lseg(current, 0, ?remaining, p) &*& 
                  mem(element, remaining) == true &*&
                  append(?processed, remaining) == xs &*&
                  (processed == nil ? pnext == phead : true);
        @*/
    {
        //@ open lseg(current, 0, remaining, p);
        void **next = *pnext;
        pnext = next;
        //@ processed = append(processed, cons(current, nil));
        //@ assert remaining == cons(current, ?new_remaining);
        //@ assert lseg((void*)*pnext, 0, new_remaining, p);
        //@ remaining = new_remaining;
    }
    {
        //@ open lseg(*pnext, 0, remaining, p);
        void *nextNext = *((void **)*pnext);
        *pnext = nextNext;
        //@ assert *((int*)element) |-> nextNext;
        //@ assert p(element);
        //@ assert lseg((void*)nextNext, 0, ?xs2, p);
        //@ assert remaining == cons(element, xs2);
        
        /*@
        // Prove that we've removed the element from the list
        if (processed == nil) {
            // If we're removing the first element
            assert pnext == phead;
            assert *phead |-> nextNext;
            assert lseg((void*)nextNext, 0, xs2, p);
            assert remove(element, xs) == xs2;
        } else {
            // If we're removing an element from the middle or end
            assert append(processed, cons(element, xs2)) == xs;
            assert append(processed, xs2) == remove(element, xs);
            lseg_merge((void*)head, (void*)nextNext, 0, processed, xs2, p);
        }
        @*/
    }
}
/*@

predicate lseg(void *first, void *last, list<void *> xs, predicate(void *) p) =
    first == last ?
        xs == nil
    :
    *((int*)first) |-> ?next &*& lseg((void*)next, last, ?xs0, p) &*& xs == cons(first, xs0) &*& p(first);

// Helper lemma to split a list segment at a specific element
lemma void lseg_split(void *from, void *to, void *element, list<void *> xs, predicate(void *) p)
    requires lseg(from, to, xs, p) &*& mem(element, xs) == true;
    ensures lseg(from, element, ?xs1, p) &*& *((int*)element) |-> ?next &*& lseg((void*)next, to, ?xs2, p) &*& 
            xs == append(xs1, cons(element, xs2)) &*& p(element);
{
    open lseg(from, to, xs, p);
    if (from == to) {
        // This case is impossible because mem(element, nil) is false
    } else {
        if (from == element) {
            close lseg(from, element, nil, p);
        } else {
            lseg_split((void*)*((int*)from), to, element, tail(xs), p);
            close lseg(from, element, cons(from, xs1), p);
        }
    }
}

// Helper lemma to merge two list segments
lemma void lseg_merge(void *from, void *mid, void *to, list<void *> xs1, list<void *> xs2, predicate(void *) p)
    requires lseg(from, mid, xs1, p) &*& lseg(mid, to, xs2, p);
    ensures lseg(from, to, append(xs1, xs2), p);
{
    open lseg(from, mid, xs1, p);
    if (from == mid) {
        // Base case: first segment is empty
    } else {
        lseg_merge((void*)*((int*)from), mid, to, tail(xs1), xs2, p);
        close lseg(from, to, append(xs1, xs2), p);
    }
}

// Helper lemma to prove that removing an element from a list preserves the lseg structure
lemma void lseg_remove_preserves(void *from, void *to, void *element, void *next, list<void *> xs, predicate(void *) p)
    requires lseg(from, element, ?xs1, p) &*& *((int*)element) |-> next &*& lseg((void*)next, to, ?xs2, p) &*& 
             xs == append(xs1, cons(element, xs2)) &*& p(element);
    ensures lseg(from, to, remove(element, xs), p) &*& *((int*)element) |-> next &*& p(element);
{
    if (xs1 == nil) {
        // If element is the first in the list
        assert from == element;
        assert remove(element, xs) == xs2;
    } else {
        // If element is in the middle or at the end
        open lseg(from, element, xs1, p);
        assert from != element;
        assert *((int*)from) |-> ?next_from;
        assert lseg((void*)next_from, element, tail(xs1), p);
        
        lseg_remove_preserves((void*)next_from, to, element, next, append(tail(xs1), cons(element, xs2)), p);
        
        assert lseg((void*)next_from, to, remove(element, append(tail(xs1), cons(element, xs2))), p);
        assert remove(element, xs) == cons(from, remove(element, append(tail(xs1), cons(element, xs2))));
        
        close lseg(from, to, remove(element, xs), p);
    }
}

@*/

void lseg_remove(void *phead, void *element)
    //@ requires *((int*)phead) |-> ?head &*& lseg((void*)head, 0, ?xs, ?p) &*& mem(element, xs) == true;
    //@ ensures *((int*)phead) |-> ?head1 &*& lseg((void*)head1, 0, remove(element, xs), p) &*& *((int*)element) |-> _ &*& p(element);
{
    void **pnext = phead;
    //@ list<void *> processed = nil;
    //@ list<void *> remaining = xs;
    
    while (*pnext != element)
        /*@
        invariant *pnext |-> ?current &*& lseg(current, 0, remaining, p) &*& 
                  mem(element, remaining) == true &*&
                  append(processed, remaining) == xs &*&
                  (processed == nil ? pnext == phead : true);
        @*/
    {
        //@ open lseg(current, 0, remaining, p);
        //@ assert current != 0;
        //@ assert *((int*)current) |-> ?next_addr;
        //@ assert lseg((void*)next_addr, 0, tail(remaining), p);
        //@ assert remaining == cons(current, tail(remaining));
        
        void **next = *pnext;
        pnext = next;
        
        //@ processed = append(processed, cons(current, nil));
        //@ remaining = tail(remaining);
    }
    {
        //@ open lseg(*pnext, 0, remaining, p);
        //@ assert *pnext == element;
        //@ assert *((int*)element) |-> ?next_element;
        //@ assert lseg((void*)next_element, 0, tail(remaining), p);
        //@ assert remaining == cons(element, tail(remaining));
        
        void *nextNext = *((void **)*pnext);
        *pnext = nextNext;
        
        /*@
        if (processed == nil) {
            // If we're removing the first element
            assert pnext == phead;
            assert *phead |-> nextNext;
            assert lseg((void*)nextNext, 0, tail(remaining), p);
            assert remove(element, xs) == tail(remaining);
        } else {
            // If we're removing an element from the middle or end
            // First, reconstruct the original list structure
            lseg_split((void*)head, 0, element, xs, p);
            
            // Now prove that after removal, we have the correct structure
            assert lseg((void*)head, element, ?xs1, p);
            assert *((int*)element) |-> nextNext;
            assert lseg((void*)nextNext, 0, ?xs2, p);
            assert xs == append(xs1, cons(element, xs2));
            
            // Use our helper lemma to prove the final structure
            lseg_remove_preserves((void*)head, 0, element, nextNext, xs, p);
        }
        @*/
    }
}