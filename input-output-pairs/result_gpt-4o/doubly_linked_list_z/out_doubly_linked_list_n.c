#include "stdlib.h"

/*@
predicate nodes(node n, node p, dllist l) =
  n == 0 ? (p == l->tail) : 
  (n->prev |-> p &*& n->next |-> ?nn &*& 
  nodes(nn, n, l));

predicate dllist(dllist l) =
  l->head |-> ?head &*& l->tail |-> ?tail &*&
  nodes(head, 0, l);
@*/

/*@
requires dllist(arg);
ensures dllist(arg);
@*/
void reverse(dllist arg)
{
    node ptr = arg->head;
    node temp1 = 0;
    node temp2 = 0;

    /*@
    loop_invariant nodes(ptr, temp2, arg) &*& 
                    (temp2 == 0 ? arg->head == ptr : ptr->prev == temp2) &*&
                    dllist(arg);
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
