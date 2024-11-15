#include <stdlib.h>

typedef struct node {
    int item;
    struct node *next;
    struct node *prev;
} *node;

typedef struct dllist {
    node head;
    node tail;
} *dllist;

//@ predicate nodes(node n, node end) =
//@     n == end ? true : n != 0 && n->next |-> ?next &*& n->prev |-> _ &*& malloc_block_node(n) &*& nodes(next, end);

void reverse(dllist arg)
    //@ requires arg != 0 &*& nodes(arg->head, 0);
    //@ ensures nodes(arg->head, 0);
{
    node ptr = arg->head;
    node temp1 = 0;
    node temp2 = 0;
    while (ptr != 0)
        //@ invariant nodes(ptr, 0) &*& arg->head |-> ?h &*& arg->tail |-> ?t;
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
