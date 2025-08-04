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
    = no->item |-> i &*& no->next |-> ne &*& no->prev |-> pr;
    
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

fixpoint nodeptrlist nappend(nodeptrlist xs, nodeptrlist ys) {
    switch (xs) {
        case nnil: return ys;
        case ncons(x, xs0): return ncons(x, nappend(xs0, ys));
    }
}

fixpoint nodeptrlist nrev(nodeptrlist xs) {
    switch (xs) {
        case nnil: return nnil;
        case ncons(x, xs0): return nappend(nrev(xs0), ncons(x, nnil));
    }
}

lemma void append_assoc(intlist xs, intlist ys, intlist zs)
    requires true;
    ensures app(app(xs, ys), zs) == app(xs, app(ys, zs));
{
    switch (xs) {
        case inil:
        case icons(x, xs_): append_assoc(xs_, ys, zs);
    }
}

lemma void rev_append_distr(intlist xs, intlist ys)
    requires true;
    ensures rev(app(xs, ys)) == app(rev(ys), rev(xs));
{
    switch (xs) {
        case inil:
        case icons(h, t):
            rev_append_distr(t, ys);
            append_assoc(rev(ys), rev(t), icons(h, inil));
    }
}

predicate list_rev(node n, intlist a, nodeptrlist l1, nodeptrlist l2) =
    n == 0 ? a == inil &*& l1 == nnil &*& l2 == nnil
           : node(n, ?i, ?p, ?ne) &*& list_rev(p, ?ap, ?l1p, ?l2p) &*&
             a == icons(i, ap) &*& l1 == ncons(n, l1p) &*& l2 == ncons(ne, l2p);

lemma void list_rev_to_list(node n)
    requires list_rev(n, ?a, ?l1, ?l2) &*& linked(?t, l1, l2, 0);
    ensures list(n, a, l1, l2) &*& linked(t, l1, l2, 0);
{
    open list_rev(n, a, l1, l2);
    if (n != 0) {
        list_rev_to_list(n->next);
    }
    close list(n, a, l1, l2);
}

lemma void linked_uncons(node t, node h, node p, nodeptrlist l1, nodeptrlist l2)
    requires linked(t, ncons(h, l1), ncons(p, l2), p);
    ensures linked(t, l1, l2, h);
{
    open linked(t, ncons(h, l1), ncons(p, l2), p);
}

lemma void linked_cons(node t, node h, node p, nodeptrlist l1, nodeptrlist l2)
    requires linked(t, l1, l2, h);
    ensures linked(t, ncons(h, l1), ncons(p, l2), p);
{
    close linked(t, ncons(h, l1), ncons(p, l2), p);
}

@*/

// TODO: make this function pass the verification
void reverse(dllist arg)
	//@ requires dll(arg, ?alpha);
 	//@ ensures dll(arg, rev(alpha));
{
	//@ open dll(arg, alpha);
	//@ assert arg->head |-> ?orig_head &*& arg->tail |-> ?orig_tail;
	//@ assert list(orig_head, alpha, ?lambda1, ?lambda2);
	//@ assert linked(orig_tail, lambda1, lambda2, 0);
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	
	//@ close list_rev(0, inil, nnil, nnil);
	//@ close linked(orig_head, nnil, nnil, orig_head);
	
	while (ptr != 0)
	/*@
	    invariant arg->head |-> orig_head &*& arg->tail |-> orig_tail &*&
	              list(ptr, ?alpha_r, ?lambda1_r, ?lambda2_r) &*&
	              linked(orig_tail, lambda1_r, ?lambda2_r_linked, temp2) &*&
	              list_rev(temp2, ?alpha_p_rev, ?lambda1_p_rev, ?lambda2_p_rev) &*&
	              linked(orig_head, lambda1_p_rev, lambda2_p_rev, ptr) &*&
	              alpha == app(rev(alpha_p_rev), alpha_r);
	@*/
	{
		//@ open list(ptr, alpha_r, lambda1_r, lambda2_r);
		//@ assert node(ptr, ?i, ?next, ?prev) &*& list(next, ?alpha_r_tail, ?lambda1_r_tail, ?lambda2_r_tail);
		//@ assert alpha_r == icons(i, alpha_r_tail);
		//@ assert lambda1_r == ncons(ptr, lambda1_r_tail);
		//@ assert lambda2_r == ncons(prev, lambda2_r_tail);
		
		//@ linked_uncons(orig_tail, ptr, temp2, lambda1_r_tail, lambda2_r_linked);
		
		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;
		
		//@ assert node(ptr, i, temp2, temp1);
		
		//@ open list_rev(temp2, alpha_p_rev, lambda1_p_rev, lambda2_p_rev);
		//@ close list_rev(ptr, icons(i, alpha_p_rev), ncons(ptr, lambda1_p_rev), ncons(temp1, lambda2_p_rev));
		
		//@ linked_cons(orig_head, ptr, temp1, lambda1_p_rev, lambda2_p_rev);
		
		ptr = temp1;
		
		// The `temp2` for the next iteration is the old `ptr`.
		// In the modified node `ptr`, its `prev` field now holds `temp1`, which is the new `ptr`.
		// So we can't just read `ptr->prev`. We use the value of the old `ptr`.
		temp2 = ptr == 0 ? temp2 : ptr->prev;
		
		//@ rev_append_distr(rev(alpha_p_rev), icons(i, inil));
		//@ append_assoc(rev(alpha_p_rev), icons(i, inil), alpha_r_tail);
	}
	
	//@ open list(0, _, _, _);
	//@ assert linked(orig_tail, nnil, _, temp2);
	//@ assert orig_tail == temp2;
	
	//@ list_rev_to_list(temp2);
	
	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
	
	//@ close dll(arg, rev(alpha));
}