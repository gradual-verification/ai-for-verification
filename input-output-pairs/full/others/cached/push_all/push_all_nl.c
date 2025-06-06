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
The stack_get_count function gets the number of nodes in a stack,
by iteratively traversing over the stack till the end. 

@param stack - pointer to the stack
*/
int stack_get_count(struct stack *stack)
{
    struct node *head = stack->head;
    struct node *n = head;
    int i = 0;
    while (n != 0)
    {
        n = n->next;
        i++;
    }
    return i;
}

/***
 * Description:
The stack_push_all function pushes all elements in the other stack to the head of the given stack. 

@param stack - pointer to the given stack
@param other - pointer to the other stack

It first traverses over the other stack to go to its end; Then, it links the end of other stack
to the head of given stack, and let the new stack's head be the head of the other stack.
*/
void stack_push_all(struct stack *stack, struct stack *other)
{
    struct node *head0 = other->head;
    free(other);
    struct node *n = head0;
    if (n != 0) {
        while (n->next != 0)
        {
            n = n->next;
        }
        n->next = stack->head;
        stack->head = head0;
    }
}