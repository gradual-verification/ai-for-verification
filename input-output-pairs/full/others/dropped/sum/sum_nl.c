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
The nodes_get_sum function gets the sum of value in the linked list starting with a given node. 
The value in each node is bigger or equal to 0. 

@param nodes - pointer to the starting node
*/
int nodes_get_sum(struct node *nodes)
{
    int result = 0;
    if (nodes != 0) {
        result = nodes_get_sum(nodes->next);
        if (result > INT_MAX - nodes->value)
            abort();
        result += nodes->value;
    }
    return result;
}

/***
 * Description:
The stack_get_sum function gets the sum of value in the elements of a given stack 
The value in each node in the stack is bigger or equal to 0. 

@param nodes - pointer to the given stack
*/
int stack_get_sum(struct stack *stack)
{
    int result = nodes_get_sum(stack->head);
    return result;
}

/***
 * Description:
The stack_dispose function iteratively frees the memory of an entire 
stack including all the nodes in its linked list. 

@param stack - pointer to the stack to be deleted.
*/
void stack_dispose(struct stack *stack)
{
    struct node *n = stack->head;
    while (n != 0)
    {
        struct node *next = n->next;
        free(n);
        n = next;
    }
    free(stack);
}
