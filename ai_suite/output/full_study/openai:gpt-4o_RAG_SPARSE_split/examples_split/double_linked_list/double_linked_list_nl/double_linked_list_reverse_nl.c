#include "stdlib.h"

/* VeriFast annotations for doubly linked list reversal */

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
predicate dll_nodes(node n, node prev, list<int> vs) =
    n == 0 ?
        vs == nil
    :
        n->item |-> ?v &*& n->next |-> ?next &*& n->prev |-> prev &*& malloc_block_node(n) &*&
        dll_nodes(next, n, ?vs0) &*& vs == cons(v, vs0);

predicate dllist(dllist l, list<int> vs) =
    l->head |-> ?head &*& l->tail |-> ?tail &*& malloc_block_dllist(l) &*&
    dll_nodes(head, 0, vs) &*& (vs == nil ? head == 0 &*& tail == 0 : true);
@*/

// TODO: make this function pass the verification
void reverse(dllist arg)
    //@ requires dllist(arg, ?vs);
    //@ ensures dllist(arg, reverse(vs));
{
    //@ open dllist(arg, vs);
    node ptr = arg->head;
    node temp1 = 0;
    node temp2 = 0;
    while (ptr != 0)
        //@ invariant dll_nodes(ptr, temp2, ?vs1) &*& dll_nodes(temp1, 0, ?vs2) &*& vs == append(reverse(vs1), vs2);
    {
        //@ open dll_nodes(ptr, temp2, vs1);
        temp1 = ptr->next;
        temp2 = ptr->prev;
        ptr->next = temp2;
        ptr->prev = temp1;
        ptr = temp1;
        //@ close dll_nodes(temp2, ptr, cons(ptr->item, vs1));
    }
    temp1 = arg->head;
    temp2 = arg->tail;
    arg->head = temp2;
    arg->tail = temp1;
    //@ close dllist(arg, reverse(vs));
}