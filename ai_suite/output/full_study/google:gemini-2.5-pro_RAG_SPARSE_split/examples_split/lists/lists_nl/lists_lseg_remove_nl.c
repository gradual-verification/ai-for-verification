#include "prelude.h"

/*@
predicate lseg(void *from, void *to, list<void *> vs) =
    from == to ?
        vs == nil
    :
        from != 0 &*&
        pointer(from, ?next) &*&
        lseg(next, to, ?vs_tail) &*&
        vs == cons(from, vs_tail);

predicate path(void **from, void **to, list<void *> vs) =
    from == to ?
        vs == nil
    :
        *from |-> ?h &*& h != 0 &*&
        path((void **)h, to, ?vs_tail) &*&
        vs == cons(h, vs_tail);

lemma void path_extend(void **from, void **to)
    requires path(from, to, ?vs) &*& *to |-> ?h &*& h != 0;
    ensures path(from, (void **)h, append(vs, cons(h, nil)));
{
    open path(from, to, vs);
    if (from == to) {
        close path((void **)h, (void **)h, nil);
        close path(from, (void **)h, cons(h, nil));
    } else {
        path_extend((void **)*from, to);
        close path(from, (void **)h, cons(*from, append(tail(vs), cons(h, nil))));
    }
}

lemma void path_close(void **from, void **to)
    requires path(from, to, ?prefix) &*& *to |-> ?end_node;
    ensures *from |-> ?start_node &*& lseg(start_node, end_node, prefix);
{
    open path(from, to, prefix);
    if (from == to) {
        close lseg(end_node, end_node, nil);
    } else {
        path_close((void **)*from, to);
        close lseg(*from, end_node, prefix);
    }
}

lemma void lseg_append(void *n1, void *n2, void *n3)
    requires lseg(n1, n2, ?vs1) &*& lseg(n2, n3, ?vs2);
    ensures lseg(n1, n3, append(vs1, vs2));
{
    open lseg(n1, n2, vs1);
    if (n1 != n2) {
        lseg_append(n1->next, n2, n3);
        close lseg(n1, n3, append(vs1, vs2));
    }
}
@*/

// TODO: make this function pass the verification
/* Description
    - Behavior: This function removes a specific element from the list segment starting from *phead*.
    - Parameters: *phead* is a pointer to the head of the list segment, *element* is the node that needs to be removed

It requires that element is part of the list segment starting from *phead*.
IT ensures that The list segment doesn't have element anymore.
*/
void lseg_remove(void *phead_void, void *element)
    //@ requires pointer_((void **)phead_void, ?head) &*& lseg(head, ?last, ?vs) &*& mem(element, vs) == true;
    //@ ensures pointer_((void **)phead_void, ?new_head) &*& lseg(new_head, last, remove(element, vs)) &*& pointer(element, _);
{
    void **phead = (void **)phead_void;
    void **pnext = phead;
    //@ close path(phead, phead, nil);
    while (*pnext != element)
        /*@
        invariant
            path(phead, pnext, ?prefix) &*&
            !mem(element, prefix) &*&
            *pnext |-> ?curr &*&
            lseg(curr, last, ?suffix) &*&
            vs == append(prefix, suffix) &*&
            mem(element, suffix) == true;
        @*/
    {
        //@ open lseg(curr, last, suffix);
        //@ mem_remove(element, suffix);
        //@ assert curr != element;
        //@ path_extend(phead, pnext);
        void **next = *pnext;
        pnext = next;
    }
    //@ open path(phead, pnext, ?prefix);
    //@ assert *pnext |-> element;
    //@ open lseg(element, last, ?suffix);
    //@ assert pointer(element, ?element_next) &*& lseg(element_next, last, ?suffix_tail);
    {
        void *nextNext = *((void **)*pnext);
        *pnext = nextNext;
    }
    //@ path_close(phead, pnext);
    //@ assert *phead |-> ?new_head &*& lseg(new_head, element_next, prefix);
    //@ lseg_append(new_head, element_next, last);
    //@ assert vs == append(prefix, cons(element, suffix_tail));
    //@ assert remove(element, vs) == append(prefix, suffix_tail);
    //@ close pointer_((void **)phead_void, new_head);
}