#include "stdlib.h"

// the value in each node is bigger or equal to 0
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

@param nodes - pointer to the starting node

It makes sure that the nodes are not changed and the return value is the sum of the values in the nodes.
*/
int nodes_get_sum(struct node *node)
{
    int result = 0;
    if (node != 0) {
        int tailSum = nodes_get_sum(node->next);
        result = node->value + tailSum;
    }
    return result;
}

/***
 * Description:
The stack_get_sum function gets the sum of value in the elements of a given stack 

@param nodes - pointer to the given stack

It makes sure that the stack is unchanged and the return value is the sum of the values in the elements of the stack.
*/
int stack_get_sum(struct stack *stack)
{
    int result = nodes_get_sum(stack->head);
    return result;
}