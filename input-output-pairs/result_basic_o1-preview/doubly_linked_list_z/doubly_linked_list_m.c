typedef struct node {
	int item;
	struct node *next;
	struct node *prev;
} *node;

/*@
predicate node(node no, int i, node ne, node pr)
    = ne == 0 ? no->next |-> ne &*& no->item |-> i &*& no->prev |-> pr
              : no->item |-> i &*& no->next |-> ne &*& no->prev |-> pr &*& malloc_block_node(no);
@*/

typedef struct dllist {
	node head;
	node tail;
} *dllist;

/*@
inductive intlist = | inil | icons(int, intlist);

predicate nodes(node n, intlist values)
    = n == 0 ? values == inil
    : node(n, ?v, ?next, ?prev) &*& nodes(next, ?rest) &*& values == icons(v, rest);

/* Reverse the intlist */
fixpoint intlist rev(intlist l) {
    switch (l) {
        case inil: return inil;
        case icons(h, t): return app(rev(t), icons(h, inil));
    }
}

fixpoint intlist app(intlist a, intlist b) {
    switch (a) {
        case inil: return b;
        case icons(h, t): return icons(h, app(t, b));
    }
}

predicate dll(dllist d, intlist values)
    = d->head |-> ?h &*& d->tail |-> ?t &*& nodes(h, values) &*& t == last_node(h);

/* Function to find the last node of the list */
fixpoint node last_node(node n) {
    switch (n) {
        case 0: return 0;
        default:
            return n->next == 0 ? n : last_node(n->next);
    }
}
@*/

void reverse(dllist arg)
    //@ requires dll(arg, ?alpha);
    //@ ensures dll(arg, rev(alpha));
{
    //@ open dll(arg, alpha);
    node ptr = arg->head;
    node temp1;
    node temp2 = 0;
    node prev = 0;
    /*@ 
    predicate_family_instance nodes(next_node)(node n1, node n2) =
        node(n1, ?i, ?nxt, ?prv) &*& n1->next |-> nxt &*& n1->prev |-> prv;
    @*/
    while(ptr != 0)
    //@ invariant nodes(ptr, ?rest_values) &*& ptr->prev |-> ?prev &*& temp2 == prev &*& prev == ptr->prev;
    {
        //@ open nodes(ptr, rest_values);
        temp1 = ptr->next;
        ptr->next = ptr->prev;
        ptr->prev = temp1;
        //@ ptr->next |-> ptr->prev; ptr->prev |-> temp1;
        prev = ptr;
        ptr = temp1;
    }
    temp1 = arg->head;
    temp2 = arg->tail;
    arg->head = temp2;
    arg->tail = temp1;
    //@ close dll(arg, rev(alpha));
}

int main()
    //@ requires true;
    //@ ensures true;
{
    return 0;
}
