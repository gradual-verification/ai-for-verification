/*

Full functional correctness proof of doubly-linked list reversal
Stephan van Staden, 2009

*/


typedef struct node {
	int item;
	struct node *next;
	struct node *prev;
} *node;

/*@

predicate node(node no, int i, node ne, node pr)
    = no->item |-> i &*& no->next |-> ne &*& no->prev |-> pr &*& malloc_block_node(no);

@*/

typedef struct dllist {
	node head;
	node tail;
} *dllist;

/*@

inductive intlist = | inil | icons(int, intlist);

inductive nodeptrlist = | nnil | ncons(node , nodeptrlist);

predicate linked(node l2, nodeptrlist lambda1, nodeptrlist lambda2, node l3)
    = lambda1 == nnil ? l2 == l3 &*& lambda2 == nnil
                      : linked(l2, ?lambda1p, ?lambda2p, ?l) &*& lambda2 == ncons(l3, lambda2p) &*& lambda1 == ncons(l, lambda1p);

predicate list(node l1, intlist alpha, nodeptrlist lambda1, nodeptrlist lambda2)
    = l1 == 0 ? alpha == inil &*& lambda1 == nnil &*& lambda2 == nnil
                 : node(l1, ?i, ?n, ?p) &*& list(n, ?alphap, ?lambda1p, ?lambda2p) &*& alpha == icons(i, alphap) &*& lambda1 == ncons(l1, lambda1p) &*& lambda2 == ncons(p, lambda2p); 

predicate dll(dllist d, intlist alpha)
    = d->head |-> ?l1 &*& d->tail |-> ?l2 &*& list(l1,alpha,?lambda1,?lambda2) &*& linked(l2,lambda1,lambda2,0) &*& malloc_block_dllist(d);

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

// Predicate for a list segment traversed via 'prev' pointers.
// This represents a list segment whose 'next' and 'prev' pointers have been swapped.
predicate list_reversed(node l1, intlist alpha, nodeptrlist lambda1, nodeptrlist lambda2) =
    l1 == 0 ?
        alpha == inil &*& lambda1 == nnil &*& lambda2 == nnil
    :
        node(l1, ?i, ?n, ?p) &*&
        list_reversed(p, ?alphap, ?lambda1p, ?lambda2p) &*&
        alpha == icons(i, alphap) &*&
        lambda1 == ncons(l1, lambda1p) &*&
        lambda2 == ncons(n, lambda2p);

lemma void app_assoc(intlist l1, intlist l2, intlist l3)
    requires true;
    ensures app(app(l1, l2), l3) == app(l1, app(l2, l3));
{
    switch (l1) {
        case inil:
        case icons(h, t):
            app_assoc(t, l2, l3);
    }
}

lemma void rev_append(intlist l1, intlist l2)
    requires true;
    ensures rev(app(l1, l2)) == app(rev(l2), rev(l1));
{
    switch (l1) {
        case inil:
        case icons(h, t):
            rev_append(t, l2);
            app_assoc(rev(l2), rev(t), icons(h, inil));
    }
}

// After reversal, a 'list_reversed' is equivalent to a 'list'.
lemma void list_reversed_to_list(node l1)
    requires list_reversed(l1, ?alpha, ?lambda1, ?lambda2) &*& linked(?l2, lambda1, lambda2, 0);
    ensures list(l1, alpha, lambda1, lambda2) &*& linked(l2, lambda1, lambda2, 0);
{
    open list_reversed(l1, alpha, lambda1, lambda2);
    if (l1 != 0) {
        open linked(l2, lambda1, lambda2, 0);
        list_reversed_to_list(l1->prev);
        close list(l1, alpha, lambda1, lambda2);
    } else {
        open linked(l2, lambda1, lambda2, 0);
        close list(0, inil, nnil, nnil);
    }
}

@*/


// TODO: make this function pass the verification
void reverse(dllist arg)
	//@ requires dll(arg, ?alpha);
 	//@ ensures dll(arg, rev(alpha));
{
	//@ open dll(arg, alpha);
	node orig_head = arg->head;
	node orig_tail = arg->tail;
	//@ list_reversed_to_list(0);
	//@ rev_append(inil, alpha);
	//@ app_assoc(inil, inil, inil);

	node ptr = arg->head;
	node prev = 0;
	node temp1 = 0;
	node temp2 = 0;
	while (ptr != 0)
		/*@
		invariant
		    arg->head |-> orig_head &*& arg->tail |-> orig_tail &*&
		    list(ptr, ?alpha_todo, ?lambda1_todo, ?lambda2_todo) &*&
		    linked(orig_tail, lambda1_todo, lambda2_todo, prev) &*&
		    list_reversed(prev, rev(?alpha_done), ?lambda1_done, ?lambda2_done) &*&
		    linked(orig_head, lambda1_done, lambda2_done, ptr) &*&
		    alpha == append(alpha_done, alpha_todo);
		@*/
	{
		//@ open list(ptr, alpha_todo, lambda1_todo, lambda2_todo);
		//@ assert node(ptr, ?i, ?n, ?p);
		//@ assert p == prev;
		//@ open linked(orig_tail, lambda1_todo, lambda2_todo, prev);

		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;

		//@ rev_append(alpha_done, icons(i, inil));
		//@ close list_reversed(ptr, rev(append(alpha_done, icons(i, inil))), ncons(ptr, lambda1_done), ncons(temp2, lambda2_done));
		//@ close linked(orig_head, ncons(ptr, lambda1_done), ncons(temp2, lambda2_done), temp1);

		prev = ptr;
		ptr = temp1;
	}

	//@ open list_reversed(prev, rev(alpha), ?lambda1, ?lambda2);
	//@ open linked(orig_head, lambda1, lambda2, 0);
	//@ assert prev == orig_tail;

	//@ list_reversed_to_list(prev);

	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;

	//@ close dll(arg, rev(alpha));
}