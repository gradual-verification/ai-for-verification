```c
#include "stdlib.h"

/*@
predicate node(struct node *n; struct node *next, struct node *prev) =
    n->next |-> next &*& n->prev |-> prev &*& malloc_block_node(n);

predicate nodes(struct node *n) =
    n == 0 ? emp :
    node(n, ?next, ?prev) &*& nodes(next);

predicate dllist(struct dllist *l) =
    l->head |-> ?head &*& l->tail |-> ?tail &*& malloc_block_dllist(l) &*& nodes(head);
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
requires dllist(arg);
ensures dllist(arg);
@*/
void reverse(dllist arg)
{
    //@ open dllist(arg);
    node ptr = arg->head;
    node temp1 = 0;
    node temp2 = 0;
    while (ptr != 0)
    //@ invariant nodes(ptr);
    {
        //@ open nodes(ptr);
        node next = ptr->next;
        node prev = ptr->prev;
        ptr->next = prev;
        ptr->prev = next;
        //@ close node(ptr, ptr->next, ptr->prev);
        //@ close nodes(ptr);
        ptr = next;
    }
    temp1 = arg->head;
    temp2 = arg->tail;
    arg->head = temp2;
    arg->tail = temp1;
    //@ close dllist(arg);
}

/*@
requires emp;
ensures emp;
@*/
int main()
{
    return 0;
}
```
