typedef struct node {
    int item;
    struct node *next;
    struct node *prev;
} *node;

/*@
predicate node(node no; int i, node ne, node pr)
    = no->item |-> i &*& no->next |-> ne &*& no->prev |-> pr;
@*/

typedef struct dllist {
    node head;
    node tail;
} *dllist;

/*@
inductive intlist = inil | icons(int, intlist);

fixpoint intlist append(intlist l1, intlist l2) {
    switch (l1) {
        case inil: return l2;
        case icons(x, xs): return icons(x, append(xs, l2));
    }
}

fixpoint intlist rev(intlist l1) {
    switch (l1) {
        case inil: return inil;
        case icons(x, xs): return append(rev(xs), icons(x, inil));
    }
}

predicate dll(node n; intlist alpha)
    = n == 0 ? alpha == inil
    : node(n, ?i, ?nxt, ?prv)
        &*& dll(nxt, ?rest)
        &*& alpha == icons(i, rest);

predicate dllrev(node from, node to; intlist alpha)
    = from == to ? alpha == inil
    : node(from, ?i, ?nxt, ?prv)
        &*& from->next |-> prv &*& from->prev |-> nxt
        &*& dllrev(nxt, to, ?rest)
        &*& alpha == icons(i, rest);
        
predicate dllist(dllist d; intlist alpha)
    = d->head |-> ?h &*& d->tail |-> ?t
        &*& dll(h, alpha)
        &*& t == 0 ? alpha == inil : true;
@*/

void reverse(dllist arg)
    //@ requires dllist(arg, ?alpha);
    //@ ensures dllist(arg, rev(alpha));
{
    node ptr = arg->head;
    node temp = 0;
    while (ptr != 0)
    //@ invariant dllrev(arg->head, ptr, ?alpha1) &*& dll(ptr, ?alpha2) &*& alpha == append(rev(alpha1), alpha2);
    {
        temp = ptr->prev;
        ptr->prev = ptr->next;
        ptr->next = temp;
        ptr = ptr->prev;
    }
    temp = arg->head;
    arg->head = arg->tail;
    arg->tail = temp;
}

int main()
    //@ requires true;
    //@ ensures true;
{
    return 0;
}
