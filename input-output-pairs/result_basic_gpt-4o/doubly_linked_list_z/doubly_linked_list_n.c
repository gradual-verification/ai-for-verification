/*@

predicate node(node n; int v, node next, node prev) =
    n->item |-> v &*& n->next |-> next &*& n->prev |-> prev;

predicate nodes(node start, node end) =
    start == end ? true : node(start, ?v, ?next, ?prev) &*& nodes(next, end);

predicate dllist(dllist dl; node head, node tail) =
    dl->head |-> head &*& dl->tail |-> tail &*& nodes(head, 0);

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
requires dllist(arg, ?head, ?tail);
ensures dllist(arg, tail, head);
@*/
void reverse(dllist arg)
{
    node ptr = arg->head;
    node temp1 = 0;
    node temp2 = 0;
    /*@
    loop_invariant nodes(ptr, 0) &*& nodes(arg->head, ptr) &*&
                    temp1 == 0 &*& temp2 == 0 &*&
                    dllist(arg, ?current_head, ?current_tail);
    @*/
    while (ptr != 0)
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

/***
 * Description:
The default main function, doing nothing.
*/
int main()
{
    return 0;
}
