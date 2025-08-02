/*

Full functional correctness proof of doubly-linked list reversal
Stephan van Staden, 2009

*/

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
// Define a predicate for a doubly-linked list segment
predicate dllseg(node first, node last, node before_first, node after_last; list<int> values) =
    first == after_last ?
        values == nil &*& last == before_first
    :
        first != 0 &*& 
        first->item |-> ?item &*& 
        first->next |-> ?next &*& 
        first->prev |-> before_first &*& 
        malloc_block_node(first) &*&
        dllseg(next, last, first, after_last, ?tail_values) &*&
        values == cons(item, tail_values);

// Define a predicate for a complete doubly-linked list
predicate dll(dllist list; list<int> values) =
    list->head |-> ?head &*&
    list->tail |-> ?tail &*&
    malloc_block_dllist(list) &*&
    dllseg(head, tail, 0, 0, values);

// Lemma to prove that reversing a list twice gives the original list
lemma void reverse_reverse<t>(list<t> xs);
    requires true;
    ensures reverse(reverse(xs)) == xs;

// Lemma to help with the reversal proof
lemma void dllseg_reverse(node first, node last, node before_first, node after_last, list<int> values)
    requires dllseg(first, last, before_first, after_last, values);
    ensures dllseg(last, first, after_last, before_first, reverse(values));
{
    open dllseg(first, last, before_first, after_last, values);
    if (first == after_last) {
        close dllseg(last, first, after_last, before_first, nil);
    } else {
        dllseg_reverse(first->next, last, first, after_last, tail(values));
        close dllseg(last, first, after_last, before_first, reverse(values));
    }
}
@*/

/***
 * Description:
 * The `reverse` function reverses the doubly linked list.
 *
 * @param arg: the head of a given doubly linked list
 * 
 * The function ensures that the doubly linked list has its values reversed.
 */
void reverse(dllist arg)
//@ requires dll(arg, ?values);
//@ ensures dll(arg, reverse(values));
{
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	//@ open dll(arg, values);
	//@ assert dllseg(ptr, ?tail, 0, 0, values);
	
	while (ptr != 0)
	//@ invariant ptr == 0 ? dllseg(arg->head, arg->tail, 0, 0, reverse(values)) : dllseg(arg->head, ptr, 0, temp2, ?prefix) &*& dllseg(ptr, arg->tail, temp2, 0, ?suffix) &*& values == append(prefix, suffix) &*& temp2 == ptr->prev;
	{
		//@ if (ptr != 0) open dllseg(ptr, arg->tail, temp2, 0, suffix);
		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;
		//@ if (temp1 == 0) close dllseg(ptr, ptr, temp1, temp2, nil);
		//@ if (temp1 != 0) close dllseg(ptr, ptr, temp1, temp2, nil);
		
		//@ if (temp1 == 0) { 
		//@   assert suffix == cons(ptr->item, nil);
		//@   assert ptr == arg->tail;
		//@ }
		
		ptr = temp1;
		
		//@ if (temp1 == 0) {
		//@   dllseg_reverse(arg->head, arg->tail, 0, 0, values);
		//@ }
	}
	
	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
	
	//@ close dll(arg, reverse(values));
}