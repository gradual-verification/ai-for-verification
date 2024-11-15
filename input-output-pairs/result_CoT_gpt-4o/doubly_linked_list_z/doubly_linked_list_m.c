#include <stdlib.h>

typedef struct node {
    int item;
    struct node *next;
    struct node *prev;
} *node;

/*@
predicate node(node no, int i, node ne, node pr)
    = no->item |-> i &*& no->next |-> ne &*& no->prev |-> pr;
@*/

typedef struct dllist {
    node head;
    node tail;
} *dllist;

/*@
inductive intlist = | inil | icons(int, intlist);

inductive nodeptrlist = | nnil | ncons(node, nodeptrlist);

predicate linked(node l2, nodeptrlist lambda1, nodeptrlist lambda2, node l3)
    = lambda1 == nnil ? l2 == l3 &*& lambda2 == nnil
                      : linked(l2, ?lambda1p, ?lambda2p, ?l) &*& lambda2 == ncons(l3, lambda2p) &*& lambda1 == ncons(l, lambda1p);

predicate list(node l1, intlist alpha, nodeptrlist lambda1, nodeptrlist lambda2)
    = l1 == 0 ? alpha == inil &*& lambda1 == nnil &*& lambda2 == nnil
              : node(l1, ?i, ?n, ?p) &*& list(n, ?alphap, ?lambda1p, ?lambda2p) &*& alpha == icons(i, alphap) &*& lambda1 == ncons(l1, lambda1p) &*& lambda2 == ncons(p, lambda2p); 

predicate dll(dllist d, intlist alpha)
    = d->head |-> ?l1 &*& d->tail |-> ?l2 &*& list(l1,alpha,?lambda1,?lambda2) &*& linked(l2,lambda1,lambda2,0);
@*/

/*@
fixpoint intlist app(intlist l1, intlist l2) {
  switch (l1) {
    case inil: return l2;
    case icons(x, v): return icons(x, app(v, l2));
  }
}

fixpoint intlist rev(intlist l) {
  switch (l) {
    case inil: return inil;
    case icons(x, v): return app(rev(v), icons(x, inil));
  }
}
@*/

void reverse(dllist arg)
//@ requires dll(arg, ?alpha);
//@ ensures dll(arg, rev(alpha));
{
    node ptr = arg->head;
    node temp1 = 0;
    node temp2 = 0;
    /*@
    predicate invariant(node p, node t1, node t2, intlist a) =
        ptr == 0 ? a == inil : list(ptr, a, ?lambda1, ?lambda2) &*& linked(t2, lambda1, lambda2, 0);

    predicate property(node p, node t1, node t2, dllist a) =
        a->head |-> t1 &*& a->tail |-> t2 &*& invariant(p, t1, t2, alpha);
    @*/
    //@ assert invariant(ptr, temp1, temp2, alpha);
    while (ptr != 0)
    /*@
    requires node(ptr, ?item, ?next, ?prev) &*& list(next, ?next_alpha, ?next_lambda1, ?next_lambda2) &*& linked(temp2, next_lambda1, next_lambda2, 0);
    ensures node(ptr, ?item2, ?prev, ?next2) &*& list(next2, ?next_alpha2, ?next_lambda1_2, ?next_lambda2_2);
    @*/
    {
        //@ open node(ptr, item, next, prev);
        temp1 = ptr->next;
        temp2 = ptr->prev;
        ptr->next = temp2;
        ptr->prev = temp1;
        ptr = temp1;
        //@ close node(ptr, item, temp2, temp1);
    }
    temp1 = arg->head;
    temp2 = arg->tail;
    arg->head = temp2;
    arg->tail = temp1;
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}
