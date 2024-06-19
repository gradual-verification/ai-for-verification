#include "stdlib.h"
#include "bool.h"
#include "lists.h"

/*@

lemma void lseg_append(void *n1)
    requires lseg(n1, ?n2, ?xs0, ?p) &*& lseg(n2, ?n3, ?xs1, p) &*& lseg(n3, 0, ?xs2, p);
    ensures lseg(n1, n3, append(xs0, xs1), p) &*& lseg(n3, 0, xs2, p);
{
    open lseg(n1, n2, xs0, p);
    if (n1 == n2) {
    } else {
        assert pointer(n1, ?n1Next);
        lseg_append(n1Next);
        if (n3 != 0) {
            open lseg(n3, 0, xs2, p);
            pointer_distinct(n1, n3);
            close lseg(n3, 0, xs2, p);
        }
        close lseg(n1, n3, append(xs0, xs1), p);
    }
}

lemma void lseg_append_final(void *n1)
    requires lseg(n1, ?n2, ?xs0, ?p) &*& lseg(n2, 0, ?xs1, p);
    ensures lseg(n1, 0, append(xs0, xs1), p);
{
    close lseg(0, 0, nil, p);
    lseg_append(n1);
    open lseg(0, 0, nil, p);
}

lemma void lseg_add(void *n1)
    requires lseg(n1, ?n2, ?xs0, ?p) &*& pointer(n2, ?n3) &*& p(n2) &*& lseg(n3, 0, ?xs1, p);
    ensures lseg(n1, n3, append(xs0, cons(n2, nil)), p) &*& lseg(n3, 0, xs1, p) &*& append(xs0, cons(n2, xs1)) == append(append(xs0, cons(n2, nil)), xs1);
{
    open lseg(n3, 0, xs1, p);
    close lseg(n3, n3, nil, p);
    if (n3 != 0) pointer_distinct(n2, n3);
    close lseg(n2, n3, cons(n2, nil), p);
    close lseg(n3, 0, xs1, p);
    lseg_append(n1);
    append_assoc(xs0, cons(n2, nil), xs1);
}

@*/

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
