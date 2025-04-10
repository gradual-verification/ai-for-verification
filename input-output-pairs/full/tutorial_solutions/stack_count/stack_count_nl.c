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
The create_stack function is a constructor for a stack data structure.

@param none

The function creates a new stack object by allocating memory for a struct stack 
and sets its head pointer to NULL. The function takes no parameters and 
returns the newly created stack.
*/
struct stack *create_stack()
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0) { abort(); }
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
    if (n == 0) { abort(); }
    n->next = stack->head;
    n->value = value;
    stack->head = n;
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

/***
 * Description:
 * a predicate function for an input. Currently no restriction.
 */
typedef bool int_predicate(int x);

/***
 * Description:
The nodes_filter function filters nodes based on a predicate.

@param n - A pointer to the node.
@param p - A predicate function to determine whether to keep a node.
@return - A pointer to the head of the filtered nodes list.

This function recursively filters the linked list of nodes, keeping only those
nodes for which the predicate function returns true. It frees the memory of the nodes
that do not satisfy the predicate.
*/
struct node *nodes_filter(struct node *n, int_predicate *p)
{
    if (n == 0)
    {
        return 0;
    }
    else
    {
        bool keep = p(n->value);
        if (keep)
        {
            struct node *next = nodes_filter(n->next, p);
            n->next = next;
            return n;
        }
        else
        {
            struct node *next = n->next;
            free(n);
            struct node *result = nodes_filter(next, p);
            return result;
        }
    }
}

/***
 * Description:
The stack_filter function filters the stack based on a predicate.

@param stack - A pointer to the stack.
@param p - A predicate function to determine whether to keep a node.

This function filters the nodes in the stack using the given predicate function.
It updates the stack to contain only the nodes that satisfy the predicate.
*/
void stack_filter(struct stack *stack, int_predicate *p)
{
    struct node *head = nodes_filter(stack->head, p);
    stack->head = head;
}

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

/***
 * Description:
The stack_dispose function iteratively frees the memory of an entire 
stack including all the nodes in its linked list. 

@param stack - pointer to the stack to be deleted.
*/
void stack_dispose_itr(struct stack *stack)
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