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
/*@
inductive ints = ints_nil | ints_cons(int, ints);
predicate nodes(struct node *node, ints values) =
node == 0 ?
values == ints_nil
:
node->next |-> ?next &*& node->value |-> ?value &*& malloc_block_node(node) &*&
nodes(next, ?values0) &*& values == ints_cons(value, values0);
predicate stack(struct stack *stack, ints values) =
stack->head |-> ?head &*& malloc_block_stack(stack) &*& nodes(head, values);
@*/

/***
 * Description:
The function creates a stack.

@param none

This function creates a new stack by allocating memory for
the struct stack. The parameter is void as it doesn't take
any input. It initializes the head of the stack to NULL.
*/
struct stack *create_stack()
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0)
    {
        abort();
    }
    stack->head = 0;
}

/***
 * Description:
This function pushes a new integer value onto the stack.

@param stack - A pointer to a stack
@param value - The integer value to be added on top on the stack

It takes a struct stack pointer and an integer valueas parameters.
It creates a new node to hold the value and links it to the current
head of the stack. Then, it updates the head of the stack to
point to the newly added node. The function ensuresthat the new value
is successfully added to the stack.

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
This function deletes a stack.

@param none

The function disposes of the stack by freeing the memory
allocated for the struct stack. It takes a struct stack
pointer as a parameter. The purpose of this function is to
deallocate the memory used by the stack once it is no longer
needed.
*/
void stack_dispose(struct stack *stack)
{

    free(stack);
}
