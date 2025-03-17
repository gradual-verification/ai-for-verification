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
The value in each node in the stack is bigger or equal to 0. 

@param nodes - pointer to the given stack
*/
int stack_get_sum(struct stack *stack)
{
    int result = nodes_get_sum(stack->head);
    return result;
}