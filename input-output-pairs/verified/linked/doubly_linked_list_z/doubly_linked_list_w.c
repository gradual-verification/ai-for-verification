


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


predicate dll(dllist d, intlist alpha)
    = d->head |-> ?l1 &*& d->tail |-> ?l2 &*& list(l1,alpha,?lambda1,?lambda2) &*& linked(l2,lambda1,lambda2,0);

@*/






void reverse(dllist arg)
	//@ requires dll(arg, ?alpha);
 	//@ ensures dll(arg, rev(alpha));
{
	
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;

	while (ptr != 0)
		
	{
		
		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;
		
		ptr = temp1;
  ;
	}

	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;

}
