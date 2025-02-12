#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

/***
 * Description:
The dispose_nodes function iteratively freees the nodes of a given linked list, by using a loop with a goto.

@param head: pointing to the head of the given linked list
*/
void dispose_nodes(struct node *head)
    //@ requires nodes(head);
    //@ ensures emp;
{
loop:
    if (head == 0) return;
    struct node *next = head->next;
    free(head);
    head = next;
    goto loop;
}

/***
 * Description:
The nested_blocks function tests whether the goto statement can get out of the while loop,
so it doesn't modify the given parameters.

@param n1, n2: nodes unchanged in this function
*/
void nested_blocks(struct node *n1, struct node *n2)
    //@ requires nodes(n1) &*& nodes(n2);
    //@ ensures nodes(n1) &*& nodes(n2);
{
    while (true)
    {
        goto l1;
    l2:
        goto l3;
    l1:
        goto l2;
    }
l3:
}

/***
 * Description:
The break_test function tests whether the break statement can get out of the while loop,
so it doesn't modify the given parameters.

@param n1, n2: nodes unchanged in this function
*/
void break_test(struct node *n1, struct node *n2)
    //@ requires nodes(n1) &*& nodes(n2);
    //@ ensures nodes(n1) &*& nodes(n2);
{
    while (true)
    {
        break;
    }
}
