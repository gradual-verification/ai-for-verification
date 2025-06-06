#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

struct stack {
    struct node *head;
};

/***
 * Description:
The stack_reverse function iteratively reverse the elements of a stack. 

@param stack - pointer to the stack to be reversed.

From the head to the tail of the old stack, 
it reverses each link pointer. Later, it lets the new head points to the end of original stack. 
*/
void stack_reverse(struct stack *stack)
{
    struct node *n = stack->head;
    struct node *m = 0;
    while (n != 0)
    {
        struct node *next = n->next;
        n->next = m;
        m = n;
        n = next;
    }
    stack->head = m;
}