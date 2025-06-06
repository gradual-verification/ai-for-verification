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

The function returns the newly created empty stack.
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

It makes sure that the number of elements in the stack is incremented by one.
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

It makes sure the `stack` has the number of elements in the `other` plus the number of elements in original `stack`.
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
The stack_pop function removes the top element from the non-empty stack and returns that element.

@param stack - pointer to the non-empty stack

This function ensures that the number of elements in the stack decreases by 1.
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
The stack_popn function removes the top n elements from a stack with at least n elements. 

@param stack - pointer to the stack
@param n - number of elements to be popped out, where n >= 0

The function makes sure that the number of elements in the stack decreases by n.
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

This function makes sure that the return value is still a start of a list of nodes. 
*/
struct node *nodes_filter(struct node *n, int_predicate *p)
{
    if (n == 0) {
        return 0;
    }
    else {
        bool keep = p(n->value);
        if (keep) {
            struct node *next = nodes_filter(n->next, p);
            n->next = next;
            return n;
        }
        else {
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

This function makes sure that `stack` after filtering is still a head of a stack.
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

This function makes sure that the stack is unchanged, and the return value is true if the stack is empty, false otherwise.
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

This function makes sure that the stack is unchanged, and the return value is the number of nodes in the stack.
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

The function makes sure to free the memory of each node in the list starting from n.
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

This function makes sure to free the stack.
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

This function makes sure to free the stack.
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