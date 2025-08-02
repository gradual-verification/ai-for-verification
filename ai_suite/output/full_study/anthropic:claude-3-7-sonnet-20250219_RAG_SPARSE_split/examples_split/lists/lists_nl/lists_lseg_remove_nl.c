// TODO: make this function pass the verification
/* Description
    - Behavior: This function removes a specific element from the list segment starting from *phead*.
    - Parameters: *phead* is a pointer to the head of the list segment, *element* is the node that needs to be removed

It requires that element is part of the list segment starting from *phead*.
IT ensures that The list segment doesn't have element anymore.
*/

/*@
predicate lseg(void *from, void *to; list<void*> values) =
    from == to ?
        values == nil
    :
        from != 0 &*&
        pointer(from, ?next) &*&
        lseg(next, to, ?tail_values) &*&
        values == cons(from, tail_values);

@*/

void lseg_remove(void *phead, void *element)
//@ requires lseg(*phead, 0, ?values) &*& pointer(phead, _) &*& mem(element, values) == true;
//@ ensures lseg(*phead, 0, remove(element, values)) &*& pointer(phead, _);
{
    void **pnext = phead;
    //@ open lseg(*pnext, 0, values);
    
    while (*pnext != element)
    //@ invariant pointer(pnext, ?current) &*& lseg(current, 0, ?remaining) &*& mem(element, remaining) == true &*& values == append(remove(element, take(index_of(element, values), values)), remaining);
    {
        //@ open lseg(*pnext, 0, remaining);
        void **next = *pnext;
        pnext = next;
        //@ assert mem(element, tail(remaining));
        //@ assert index_of(element, remaining) > 0;
        //@ take_plus_one(index_of(element, remaining) - 1, remaining);
        //@ assert take(index_of(element, remaining), remaining) == cons(*pnext, take(index_of(element, remaining) - 1, tail(remaining)));
        //@ assert remove(element, take(index_of(element, values), values)) == append(remove(element, take(index_of(element, values) - 1, values)), cons(*pnext, nil));
        //@ assert values == append(append(remove(element, take(index_of(element, values) - 1, values)), cons(*pnext, nil)), remaining);
        //@ append_assoc(remove(element, take(index_of(element, values) - 1, values)), cons(*pnext, nil), remaining);
        //@ assert values == append(remove(element, take(index_of(element, values) - 1, values)), append(cons(*pnext, nil), remaining));
        //@ assert append(cons(*pnext, nil), remaining) == cons(*pnext, remaining);
        //@ assert values == append(remove(element, take(index_of(element, values) - 1, values)), cons(*pnext, remaining));
        //@ assert values == append(remove(element, take(index_of(element, values) - 1, values)), cons(*pnext, remaining));
    }
    
    {
        //@ open lseg(*pnext, 0, remaining);
        void *nextNext = *((void **)*pnext);
        *pnext = nextNext;
        //@ close lseg(*pnext, 0, tail(remaining));
        //@ assert values == append(remove(element, take(index_of(element, values), values)), remaining);
        //@ assert remaining == cons(element, tail(remaining));
        //@ assert remove(element, remaining) == tail(remaining);
        //@ assert remove(element, values) == append(remove(element, take(index_of(element, values), values)), remove(element, remaining));
        //@ assert remove(element, values) == append(remove(element, take(index_of(element, values), values)), tail(remaining));
    }
}