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
The stack_pop function removes the top element 
from the non-empty stack and returns that element.

@param stack - pointer to the non-empty stack

The function takes a pointer to the stack as a parameter and 
retrieves the value of the top node. It then updates the 
head pointer of the stack to the next node and frees the 
memory of the popped node.
*/
int stack_pop(struct stack *stack)
{
    struct node *head = stack->head;
    int result = head->value;
    stack->head = head->next;
    free(head);
    return result;
}

/***
 * Description:
The stack_popn function removes the top n elements
from a stack with at least n elements. 

@param stack - pointer to the stack
@param n - number of elements to be popped out

The function iteratively calls stack_pop() function to pop elements. 
*/
void stack_popn(struct stack *stack, int n)
{
    int i = 0;
    while (i < n)
    {
        stack_pop(stack);
        i++;
    }
}