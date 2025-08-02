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

@*/


void reverse(dllist arg)
	//@ requires dll(arg, ?alpha);
 	//@ ensures dll(arg, rev(alpha));
{
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	//@ open dll(arg, alpha);
	//@ node l1 = ptr;
	//@ node l2 = 0;
	//@ open list(l1, alpha, ?lambda1, ?lambda2);
	
	//@ if (l1 == 0) {
	//@   close list(0, inil, nnil, nnil);
	//@   close linked(0, nnil, nnil, 0);
	//@   close dll(arg, rev(alpha));
	//@ } else {
	
	//@ assert node(l1, ?i, ?n, ?p);
	//@ assert list(n, ?alphap, ?lambda1p, ?lambda2p);
	//@ assert alpha == icons(i, alphap);
	//@ assert lambda1 == ncons(l1, lambda1p);
	//@ assert lambda2 == ncons(p, lambda2p);
	
	//@ nodeptrlist revlambda1 = nnil;
	//@ nodeptrlist revlambda2 = nnil;
	//@ intlist revalpha = inil;
	
	while (ptr != 0)
		//@ invariant arg->head |-> l1 &*& arg->tail |-> l2 &*& ptr |-> ?curr &*& temp1 |-> ?t1 &*& temp2 |-> ?t2 &*& 
		//@ list(curr, ?currAlpha, ?currLambda1, ?currLambda2) &*& list(0, revalpha, revlambda1, revlambda2) &*& 
		//@ linked(l2, lambda1, lambda2, 0) &*& app(rev(currAlpha), revalpha) == rev(alpha);
	{
		//@ open list(curr, currAlpha, currLambda1, currLambda2);
		//@ if (curr == 0) {
		//@   assert false;
		//@ }
		//@ assert node(curr, ?ci, ?cn, ?cp);
		//@ assert list(cn, ?cnAlpha, ?cnLambda1, ?cnLambda2);
		//@ assert currAlpha == icons(ci, cnAlpha);
		//@ assert currLambda1 == ncons(curr, cnLambda1);
		//@ assert currLambda2 == ncons(cp, cnLambda2);
		
		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;
		
		//@ close node(curr, ci, cp, cn);
		//@ close list(cp, revalpha, revlambda1, revlambda2);
		//@ revlambda1 = ncons(curr, revlambda1);
		//@ revlambda2 = ncons(cn, revlambda2);
		//@ revalpha = icons(ci, revalpha);
		
		//@ assert app(rev(cnAlpha), icons(ci, revalpha)) == app(rev(cnAlpha), app(icons(ci, inil), revalpha));
		//@ assert app(icons(ci, inil), revalpha) == icons(ci, revalpha);
		
		//@ lemma void app_assoc(intlist a, intlist b, intlist c)
		//@ requires true;
		//@ ensures app(app(a, b), c) == app(a, app(b, c));
		//@ {
		//@   switch(a) {
		//@     case inil:
		//@     case icons(x, xs): app_assoc(xs, b, c);
		//@   }
		//@ }
		
		//@ app_assoc(rev(cnAlpha), icons(ci, inil), revalpha);
		//@ assert app(rev(cnAlpha), icons(ci, revalpha)) == app(app(rev(cnAlpha), icons(ci, inil)), revalpha);
		//@ assert app(rev(cnAlpha), icons(ci, inil)) == app(rev(cnAlpha), icons(ci, inil));
		//@ assert app(app(rev(cnAlpha), icons(ci, inil)), revalpha) == app(rev(icons(ci, cnAlpha)), revalpha);
		//@ assert rev(icons(ci, cnAlpha)) == app(rev(cnAlpha), icons(ci, inil));
		//@ assert app(rev(icons(ci, cnAlpha)), revalpha) == app(rev(currAlpha), revalpha);
		
		ptr = temp1;
	}
	//@ open list(0, revalpha, revlambda1, revlambda2);
	
	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
	
	//@ close linked(temp1, revlambda1, revlambda2, 0);
	//@ close dll(arg, rev(alpha));
	//@ }
}