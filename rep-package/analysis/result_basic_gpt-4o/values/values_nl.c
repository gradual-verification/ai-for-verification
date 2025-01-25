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

// VeriFast annotations for specifications
/*@
predicate nodes(struct node *n; list<int> vs) =
    n == 0 ? vs == nil : n->next |-> ?next &*& n->value |-> ?v &*& malloc_block_node(n) &*&
    nodes(next, ?vs1) &*& vs == cons(v, vs1);

predicate stack(struct stack *s; list<int> vs) =
    s->head |-> ?head &*& malloc_block_stack(s) &*& nodes(head, vs);
@*/

// Description: The create_stack function creates a stack.

struct stack *create_stack()
//@ requires true;
//@ ensures stack(result, nil);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0)
    {
        abort();
    }
    stack->head = 0;
    return stack;
}

// Description: The stack_push function pushes a new integer value onto the stack.

void stack_push(struct stack *stack, int value)
//@ requires stack(stack, ?vs);
//@ ensures stack(stack, cons(value, vs));
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

// Description: The stack_dispose function deletes an empty stack.

void stack_dispose(struct stack *stack)
//@ requires stack(stack, nil);
//@ ensures true;
{
    free(stack);
    //@ open nodes(_, _);
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}
