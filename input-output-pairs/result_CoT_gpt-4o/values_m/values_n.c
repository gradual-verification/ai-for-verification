#include "stdlib.h"
#include "verifast.h"

// Predicate definitions
predicate nodes(struct node *n; list<int> values) =
    n == 0 ?
        values == nil
    :
        malloc_block_node(n) &*&
        n->value |-> ?v &*&
        n->next |-> ?next &*&
        nodes(next, ?vs) &*&
        values == cons(v, vs);

predicate stack(struct stack *s; list<int> values) =
    malloc_block_stack(s) &*&
    s->head |-> ?head &*&
    nodes(head, values);

// Function specifications
struct stack *create_stack()
    //@ requires true;
    //@ ensures result != 0 &*& stack(result, nil);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0)
    {
        abort();
    }
    stack->head = 0;
    return stack;
    //@ close stack(stack, nil);
}

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
    n->next = stack->head;
    n->value = value;
    stack->head = n;
    //@ close nodes(n, cons(value, values));
    //@ close stack(stack, cons(value, values));
}

void stack_dispose(struct stack *stack)
    //@ requires stack(stack, nil);
    //@ ensures true;
{
    //@ open stack(stack, nil);
    free(stack);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_dispose(s);
    return 0;
}
