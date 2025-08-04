#include "stdlib.h"

/*@
#include "list.gh"
@*/

typedef struct node {
	int item;
	struct node *next;
	struct node *prev;
} *node;


typedef struct dllist {
	node head;
	node tail;
} *dllist;

/*@

// An lseg (list segment) from p to q, where p_prev is the node preceding p.
// The segment contains the values 'vs'. The tail of the segment is 't'.
predicate lseg(node p, node p_prev, node q; list<int> vs, node t) =
    p == q ?
        vs == nil &*& t == p_prev
    :
        p->item |-> ?v &*& p->next |-> ?n &*& p->prev |-> p_prev &*& malloc_block_node(p) &*&
        lseg(n, p, q, ?rest, t) &*& vs == cons(v, rest);

// An rlseg (reversed list segment) from p to q, where p_next is the node "after" p in the original list.
// The segment contains the values 'vs'. The head of the segment is 'h'.
// In an rlseg, the 'prev' pointers link the nodes in forward order.
predicate rlseg(node p, node p_next, node q; list<int> vs, node h) =
    p == q ?
        vs == nil &*& h == p_next
    :
        p->item |-> ?v &*& p->prev |-> ?n &*& p->next |-> p_next &*& malloc_block_node(p) &*&
        rlseg(n, p, q, ?rest, h) &*& vs == cons(v, rest);

predicate dllist_pred(dllist l; list<int> vs) =
    l->head |-> ?h &*& l->tail |-> ?t &*& malloc_block_dllist(l) &*&
    lseg(h, 0, 0, vs, t);

// Lemma to prepend a node to a reversed list segment.
lemma void rlseg_cons(node p, node p_next, node q, list<int> vs, node h, node new_head, int new_v)
    requires
        rlseg(p, new_head, q, vs, h) &*&
        new_head->item |-> new_v &*& new_head->prev |-> p_next &*& new_head->next |-> p &*& malloc_block_node(new_head);
    ensures
        rlseg(new_head, p_next, q, cons(new_v, vs), h);
{
    open rlseg(new_head, p_next, q, cons(new_v, vs), h);
    close rlseg(new_head, p_next, q, cons(new_v, vs), h);
}

// Lemma to show that a reversed list segment is equivalent to a forward list segment.
lemma void rlseg_to_lseg(node p, node p_next, node q, list<int> vs, node h)
    requires rlseg(p, p_next, q, vs, h);
    ensures lseg(p, q, p_next, vs, h);
{
    open rlseg(p, p_next, q, vs, h);
    if (p != q) {
        rlseg_to_lseg(p->prev, p, q, tail(vs), h);
    }
    close lseg(p, q, p_next, vs, h);
}

@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `reverse` function reverses the doubly linked list.
 *
 * @param arg: the head of a given doubly linked list
 * 
 * The function ensures that the doubly linked list has its values reversed.
 */
void reverse(dllist arg)
    //@ requires dllist_pred(arg, ?vs);
    //@ ensures dllist_pred(arg, reverse(vs));
{
    //@ open dllist_pred(arg, vs);
    //@ node h_orig = arg->head;
    //@ node t_orig = arg->tail;
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	
	//@ close rlseg(0, h_orig, 0, nil, h_orig);
	while (ptr != 0)
	    /*@
	    invariant
	        arg->head |-> h_orig &*& arg->tail |-> t_orig &*& malloc_block_dllist(arg) &*&
	        lseg(ptr, temp2, 0, ?vs_rest, t_orig) &*&
	        rlseg(temp2, ptr, 0, ?vs_rev, h_orig) &*&
	        vs == append(reverse(vs_rev), vs_rest);
	    @*/
	{
	    //@ open lseg(ptr, temp2, 0, vs_rest, t_orig);
	    //@ int v = ptr->item;
		temp1 = ptr->next;
		// temp2 is already ptr->prev from the lseg invariant
		ptr->next = temp2;
		ptr->prev = temp1;
		
		//@ rlseg_cons(temp2, temp1, 0, vs_rev, h_orig, ptr, v);
		
		temp2 = ptr;
		ptr = temp1;
		
		//@ reverse_append(vs_rev, cons(v, nil));
		//@ append_assoc(reverse(vs_rev), cons(v, nil), tail(vs_rest));
	}
	
	//@ open rlseg(temp2, ptr, 0, vs_rev, h_orig);
	//@ assert ptr == 0;
	//@ assert vs_rev == reverse(vs);
	
	//@ rlseg_to_lseg(temp2, 0, 0, reverse(vs), h_orig);
	
	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
	
	//@ close dllist_pred(arg, reverse(vs));
}
