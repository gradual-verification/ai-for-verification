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

//@ predicate nodes(struct node *node, list<int> values) =
//@     node == 0 ?
//@         values == nil
//@     :
//@         node->next |-> ?next &*&
//@         node->value |-> ?value &*&
//@         malloc_block_node(node) &*&
//@         nodes(next, ?restvalues) &*&
//@         values == cons(value, restvalues);

//@ predicate stack(struct stack *stack, list<int> values) =
//@     stack->head |-> ?head &*&
//@     malloc_block_stack(stack) &*&
//@     nodes(head, values);

/***
 * Description:
The create_stack function creates a stack.

@param none

This function creates a new stack by allocating memory for
the struct stack. The parameter is void as it doesn't take
any input. It initializes the head of the stack to NULL.
*/
struct stack *create_stack()
    //@ requires true;
    //@ ensures stack(result, nil);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0)
    {
        abort();
    }
    //@ malloc_block_stack(stack);
    stack->head = 0;
    //@ close nodes(0, nil);
    //@ close stack(stack, nil);
    return stack;
}

/***
 * Description:
The stack_push function pushes a new integer value onto the stack.

@param stack - A pointer to a stack
@param value - The integer value to be added on top on the stack

It takes a struct stack pointer and an integer values parameters.
It creates a new node to hold the value and links it to the current
head of the stack. Then, it updates the head of the stack to
point to the newly added node. The function ensures that the new value
is successfully added to the stack.
*/
void stack_push(struct stack *stack, int value)
    //@ requires stack(stack, ?values);
    //@ ensures stack(stack, cons(value, values));
{
    //@ open stack(stack, values);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    //@ malloc_block_node(n);
    n->next = stack->head;
    n->value = value;
    //@ close nodes(n, cons(value, values));
    stack->head = n;
    //@ close stack(stack, cons(value, values));
}

/***
 * Description:
The stack_dispose function deletes a stack.

@param stack- A pointer to a stack

The function disposes of the stack by freeing the memory
allocated for the struct stack and its nodes. It takes a struct stack
pointer as a parameter. The purpose of this function is to
deallocate the memory used by the stack once it is no longer
needed.
*/
void stack_dispose(struct stack *stack)
    //@ requires stack(stack, ?values);
    //@ ensures true;
{
    //@ open stack(stack, values);
    struct node *current = stack->head;
    while(current != 0)
        //@ invariant nodes(current, ?restvalues);
    {
        //@ open nodes(current, restvalues);
        struct node *next = current->next;
        free(current);
        current = next;
    }
    //@ open nodes(0, _);
    free(stack);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    return 0;
}
