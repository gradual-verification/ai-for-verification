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
The stack_is_empty function checks if the given stack has no element,
by checking whether the head is null. 

@param stack - pointer to the stack
*/
bool stack_is_empty(struct stack *stack)
{
    struct node *head = stack->head;
    bool result = stack->head == 0;
    return result;
}

/***
 * Description:
The nodes_dispose function recursively deallocates memory 
for all nodes in a linked list starting from a given node. 

@param n - pointer to the node to be disposed.

The function takes a pointer to a node as a parameter and traverses 
the linked list by recursively calling itself on the next 
node until reaching the end of the list. The function frees 
the memory of each node as it unwinds the recursion.
*/
void nodes_dispose(struct node *n)
{
    if (n != 0) {
        nodes_dispose(n->next);
        free(n);
    }
}

/***
 * Description:
The stack_dispose function frees the memory of an entire 
stack including all the nodes in its linked list. 

@param stack - pointer to the stack to be deleted.

It takes a pointer to the stack as a parameter and calls 
nodes_dispose on the head of the stack to deallocate 
memory for all nodes. Finally, it frees the memory of the 
stack itself.
*/
void stack_dispose(struct stack *stack)
{
    nodes_dispose(stack->head);
    free(stack);
}
