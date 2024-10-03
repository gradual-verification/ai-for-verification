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
The create_stack function creates an empty stack.
 
@return - A pointer to the newly created stack.

This function allocates memory for a new stack and initializes its head to NULL.
If memory allocation fails, the program aborts.
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
The stack_push function pushes a value onto the stack.

@param stack - A pointer to the stack.
@param value - The integer value to push onto the stack.

This function allocates a new node, assigns the given value to it,
and sets the new node as the head of the stack.
If memory allocation fails, the program aborts.
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
The stack_pop function pops a value from the stack.

@param stack - A pointer to the stack.
@return - The integer value popped from the stack.

This function removes the head node from the stack, retrieves its value,
and frees the memory allocated to the head node. The stack must not be empty.
*/
int stack_pop(struct stack *stack)
{
    struct node *head = stack->head;
    int result = head->value;
    stack->head = head->next;
    free(head);
    return result;
}

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
The nodes_dispose function disposes of all nodes in a linked list.

@param n - A pointer to the head node.
 
This function recursively frees all nodes in the linked list.
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
The stack_dispose function disposes of a stack.

@param stack - A pointer to the stack.

This function frees all nodes in the stack and then frees the stack itself.
*/
void stack_dispose(struct stack *stack)
{
    nodes_dispose(stack->head);
    free(stack);
}

/***
 * Description:
The neq_20 function filters the stack based on a predicate.

@param stack - A pointer to the stack.
@param p - A predicate function to determine whether to keep a node.
 
This function filters the nodes in the stack using the given predicate function.
It updates the stack to contain only the nodes that satisfy the predicate.
*/
bool neq_20(int x) //@ : int_predicate
{
    return x != 20;
}

/***
 * Description:
The main function creates a stack, pushes some integers into it, 
filters out some integers from the stack and finally disposes the stack.
*/
int main()
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    stack_push(s, 30);
    stack_filter(s, neq_20);
    stack_dispose(s);
    return 0;
}
