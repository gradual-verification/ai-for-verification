#include "stdlib.h"

struct node
{
    struct node *next;
    int value;
};

struct stack
{
    struct node *head;
};

/***
 * Description:
The create_stack function is a constructor for a stack data structure.

@param none

The function creates a new stack object by allocating memory for a struct stack 
and sets its head pointer to NULL. The function takes no parameters and 
returns the newly created stack.
*/
struct stack *create_stack()
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0)
    {
        abort();
    }
    stack->head = 0;
    return stack;
}

/***
 * Description:
The stack_push function adds an element to the top of the stack. 

@param stack - pointer to the stack
@param value - integer value to be added to the stack

The function dynamically allocates memory for a new node, 
assigns the value to the node, and updates the head pointer 
of the stack to point to the new node. The number of elements 
in the stack is incremented by one.
*/
void stack_push(struct stack *stack, int value)
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    n->next = stack->head;
    n->value = value;
    stack->head = n;
}

/***
 * Description:
The stack_pop function removes the top element 
from the non-empty stack.

@param stack - pointer to the non-empty stack

The function takes a pointer to the stack as a parameter and 
retrieves the value of the top node. It then updates the 
head pointer of the stack to the next node, frees the 
memory of the popped node, and returns the value.
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
    if (n != 0)
    {
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

/***
 * Description:
The main function creates a stack, adds twice and removes twice,
and finally dispose the stack.
*/
int main()
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    stack_pop(s);
    stack_pop(s);
    stack_dispose(s);
    return 0;
}
