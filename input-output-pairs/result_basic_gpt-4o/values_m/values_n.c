#include "stdlib.h"

// VeriFast annotations for specifications
/*@
predicate nodes(struct node *n; list<int> vs) =
    n == 0 ? vs == nil : n->next |-> ?next &*& n->value |-> ?v &*& malloc_block_node(n) &*&
    nodes(next, ?vs1) &*& vs == cons(v, vs1);

predicate stack(struct stack *s; list<int> vs) =
    s->head |-> ?head &*& malloc_block_stack(s) &*& nodes(head, vs);
@*/

// Description: The create_stack function creates a stack.
/*@
requires true;
ensures stack(result, nil);
@*/
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

// Description: The stack_push function pushes a new integer value onto the stack.
/*@
requires stack(stack, ?vs);
ensures stack(stack, cons(value, vs));
@*/
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

// Description: The stack_dispose function deletes an empty stack.
/*@
requires stack(stack, nil);
ensures true;
@*/
void stack_dispose(struct stack *stack)
{
    free(stack);
}

int main()
{
    return 0;
}
