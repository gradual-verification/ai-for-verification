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

// Helper lemma to prove that linked is preserved when we reverse the lists
lemma void linked_reverse(node l2, nodeptrlist lambda1, nodeptrlist lambda2, node l3)
    requires linked(l2, lambda1, lambda2, l3);
    ensures linked(l3, reverse(lambda2), reverse(lambda1), l2);
{
    open linked(l2, lambda1, lambda2, l3);
    if (lambda1 == nnil) {
        // Base case: empty lists
        close linked(l3, reverse(lambda2), reverse(lambda1), l2);
    } else {
        // Recursive case
        linked_reverse(?l, ?lambda1p, ?lambda2p, l3);
        
        // Now we need to show that linked(l3, reverse(ncons(l3, lambda2p)), reverse(ncons(l, lambda1p)), l2)
        // which is linked(l3, append(reverse(lambda2p), ncons(l3, nnil)), append(reverse(lambda1p), ncons(l, nnil)), l2)
        
        // First, let's establish that reverse(ncons(x, xs)) == append(reverse(xs), ncons(x, nnil))
        assert reverse(ncons(l, lambda1p)) == append(reverse(lambda1p), ncons(l, nnil));
        assert reverse(ncons(l3, lambda2p)) == append(reverse(lambda2p), ncons(l3, nnil));
        
        // Now we can close the linked predicate with the reversed lists
        close linked(l3, reverse(lambda2), reverse(lambda1), l2);
    }
}

// Helper lemma to prove that list is preserved when we reverse the lists
lemma void list_reverse(node l1, intlist alpha, nodeptrlist lambda1, nodeptrlist lambda2)
    requires list(l1, alpha, lambda1, lambda2);
    ensures list(l1, alpha, lambda1, lambda2) &*& 
            (l1 == 0 ? true : 
                       (lambda1 == ncons(l1, ?lambda1p) &*& lambda2 == ncons(?p, ?lambda2p)));
{
    open list(l1, alpha, lambda1, lambda2);
    if (l1 == 0) {
        close list(l1, alpha, lambda1, lambda2);
    } else {
        list_reverse(?n, ?alphap, ?lambda1p, ?lambda2p);
        close list(l1, alpha, lambda1, lambda2);
    }
}

// Helper lemma to prove that when we swap next and prev pointers, we get the reversed list
lemma void reverse_dll_helper(node ptr, intlist alpha, nodeptrlist lambda1, nodeptrlist lambda2)
    requires list(ptr, alpha, lambda1, lambda2) &*& ptr != 0;
    ensures list(ptr, alpha, lambda1, lambda2);
{
    open list(ptr, alpha, lambda1, lambda2);
    if (ptr->next != 0) {
        reverse_dll_helper(ptr->next, ?alphap, ?lambda1p, ?lambda2p);
    }
    close list(ptr, alpha, lambda1, lambda2);
}

@*/

// TODO: make this function pass the verification
void reverse(dllist arg)
	//@ requires dll(arg, ?alpha);
 	//@ ensures dll(arg, rev(alpha));
{
	//@ open dll(arg, alpha);
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	
	//@ list_reverse(ptr, alpha, ?lambda1, ?lambda2);
	//@ linked_reverse(?l2, lambda1, lambda2, 0);
	
	while (ptr != 0)
	    /*@ invariant 
	        arg->head |-> ?h &*& arg->tail |-> ?t &*&
	        (ptr == 0 ? 
	            list(temp1, rev(alpha), ?lambda1_rev, ?lambda2_rev) &*& linked(temp2, lambda1_rev, lambda2_rev, 0)
	            : 
	            list(ptr, ?alpha_rest, ?lambda1_rest, ?lambda2_rest) &*& 
	            list(temp1, rev(?alpha_done), ?lambda1_done, ?lambda2_done) &*&
	            linked(temp2, lambda1_done, lambda2_done, 0) &*&
	            alpha == app(alpha_done, alpha_rest));
	    @*/
	{
	    //@ open list(ptr, alpha_rest, lambda1_rest, lambda2_rest);
		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;
		
		//@ intlist new_alpha_done = icons(ptr->item, alpha_done);
		//@ assert alpha_rest == icons(ptr->item, ?alpha_rest_tail);
		//@ assert app(alpha_done, alpha_rest) == app(alpha_done, icons(ptr->item, alpha_rest_tail));
		//@ assert app(alpha_done, icons(ptr->item, alpha_rest_tail)) == app(alpha_done, icons(ptr->item, alpha_rest_tail));
		//@ assert rev(icons(ptr->item, alpha_rest_tail)) == app(rev(alpha_rest_tail), icons(ptr->item, inil));
		
		//@ close node(ptr, ptr->item, temp2, temp1);
		//@ close list(ptr, icons(ptr->item, inil), ncons(ptr, nnil), ncons(temp1, nnil));
		
		//@ nodeptrlist new_lambda1 = ncons(ptr, lambda1_done);
		//@ nodeptrlist new_lambda2 = ncons(temp1, lambda2_done);
		
		//@ close list(temp1, alpha_rest_tail, lambda1_rest, lambda2_rest);
		
		ptr = temp1;
	}
	
	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
	
	//@ close dll(arg, rev(alpha));
}
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

// Helper lemma for app associativity
lemma void app_assoc(intlist l1, intlist l2, intlist l3)
    requires true;
    ensures app(app(l1, l2), l3) == app(l1, app(l2, l3));
{
    switch(l1) {
        case inil:
        case icons(x, xs):
            app_assoc(xs, l2, l3);
    }
}

// Helper lemma for rev of app
lemma void rev_app(intlist l1, intlist l2)
    requires true;
    ensures rev(app(l1, l2)) == app(rev(l2), rev(l1));
{
    switch(l1) {
        case inil:
            switch(l2) {
                case inil:
                case icons(y, ys):
            }
        case icons(x, xs):
            rev_app(xs, l2);
            app_assoc(rev(l2), rev(xs), icons(x, inil));
    }
}

// Helper lemma for rev of rev
lemma void rev_rev(intlist l)
    requires true;
    ensures rev(rev(l)) == l;
{
    switch(l) {
        case inil:
        case icons(x, xs):
            rev_rev(xs);
            rev_app(rev(xs), icons(x, inil));
    }
}

// Helper lemma for nodeptrlist reversal
fixpoint nodeptrlist reverse_nodeptrlist(nodeptrlist l) {
    switch(l) {
        case nnil: return nnil;
        case ncons(x, xs): return append_nodeptrlist(reverse_nodeptrlist(xs), ncons(x, nnil));
    }
}

fixpoint nodeptrlist append_nodeptrlist(nodeptrlist l1, nodeptrlist l2) {
    switch(l1) {
        case nnil: return l2;
        case ncons(x, xs): return ncons(x, append_nodeptrlist(xs, l2));
    }
}

lemma void append_nodeptrlist_assoc(nodeptrlist l1, nodeptrlist l2, nodeptrlist l3)
    requires true;
    ensures append_nodeptrlist(append_nodeptrlist(l1, l2), l3) == append_nodeptrlist(l1, append_nodeptrlist(l2, l3));
{
    switch(l1) {
        case nnil:
        case ncons(x, xs):
            append_nodeptrlist_assoc(xs, l2, l3);
    }
}

lemma void reverse_nodeptrlist_append(nodeptrlist l1, nodeptrlist l2)
    requires true;
    ensures reverse_nodeptrlist(append_nodeptrlist(l1, l2)) == append_nodeptrlist(reverse_nodeptrlist(l2), reverse_nodeptrlist(l1));
{
    switch(l1) {
        case nnil:
            switch(l2) {
                case nnil:
                case ncons(y, ys):
            }
        case ncons(x, xs):
            reverse_nodeptrlist_append(xs, l2);
            append_nodeptrlist_assoc(reverse_nodeptrlist(l2), reverse_nodeptrlist(xs), ncons(x, nnil));
    }
}

// Helper lemma for linked with reversed lists
lemma void linked_reverse(node l2, nodeptrlist lambda1, nodeptrlist lambda2, node l3)
    requires linked(l2, lambda1, lambda2, l3);
    ensures linked(l3, reverse_nodeptrlist(lambda2), reverse_nodeptrlist(lambda1), l2);
{
    open linked(l2, lambda1, lambda2, l3);
    if (lambda1 == nnil) {
        close linked(l3, reverse_nodeptrlist(lambda2), reverse_nodeptrlist(lambda1), l2);
    } else {
        linked_reverse(?l, ?lambda1p, ?lambda2p, l3);
        close linked(l3, reverse_nodeptrlist(lambda2), reverse_nodeptrlist(lambda1), l2);
    }
}

// Helper lemma for list with reversed pointers
lemma void list_reverse_pointers(node ptr, intlist alpha_rest, nodeptrlist lambda1_rest, nodeptrlist lambda2_rest, 
                                 intlist alpha_done, nodeptrlist lambda1_done, nodeptrlist lambda2_done)
    requires list(ptr, alpha_rest, lambda1_rest, lambda2_rest) &*& ptr != 0;
    ensures list(ptr, alpha_rest, lambda1_rest, lambda2_rest);
{
    open list(ptr, alpha_rest, lambda1_rest,