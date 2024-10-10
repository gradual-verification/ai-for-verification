```c CODE and SPEC
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
predicate node(node n;) = n == 0 ? true : n->next |-> ?next &*& n->prev |-> ?prev &*& malloc_block_node(n) &*& node(next) &*& node(prev);
predicate dllist(dllist dl;) = dl == 0 ? true : dl->head |-> ?head &*& dl->tail |-> ?tail &*& malloc_block_dllist(dl) &*& node(head) &*& node(tail);
@*/

/***
 * Description:
The `reverse` function reverses the order of nodes in a doubly linked list.

@param arg - The doubly linked list to be reversed.
@requires - The argument `arg` must be a valid doubly linked list.
@ensures - The order of nodes in the doubly linked list pointed to by `arg` is reversed.
*/
void reverse(dllist arg)
{
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	while (ptr != 0)
	//@requires node(ptr);
	//@ensures node(ptr);
	{
		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;
		ptr = temp1;
	}
	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
}
```
