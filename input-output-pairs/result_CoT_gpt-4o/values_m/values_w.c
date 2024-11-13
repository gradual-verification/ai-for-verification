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
        node->next |-> ?next &*& node->value |-> ?value &*&
        nodes(next, ?values0) &*& values == ints_cons(value, values0);

predicate stack(struct stack *stack, ints values) =
    stack->head |-> ?head &*& nodes(head, values);
@*/

struct stack *create_stack()
//@ requires true;
//@ ensures stack(result, ints_nil);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0)
    {
        abort();
    }
    stack->head = 0;
    return stack;
}

void stack_push(struct stack *stack, int value)
//@ requires stack(stack, ?values);
//@ ensures stack(stack, ints_cons(value, values));
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    //@ open stack(stack, values);
    n->next = stack->head;
    n->value = value;
    stack->head = n;
    //@ close nodes(n, ints_cons(value, values));
    //@ close stack(stack, ints_cons(value, values));
}

void stack_dispose(struct stack *stack)
//@ requires stack(stack, ints_nil);
//@ ensures true;
{   
    //@ open stack(stack, ints_nil);
    //@ assert stack->head |-> 0; // Ensure stack is empty before disposal
    free(stack);
}

int main()
//@ requires true;
//@ ensures true;
{
    struct stack *s = create_stack();
    stack_push(s, 42);
    stack_push(s, 13);
    stack_push(s, 37);
    
    // Must pop all elements before stack_dispose
    //@ open stack(s, _);
    //@ open nodes(_, ints_cons(37, ints_cons(13, ints_cons(42, ints_nil))));
    //@ open nodes(_, ints_cons(13, ints_cons(42, ints_nil)));
    //@ open nodes(_, ints_cons(42, ints_nil));
    //@ open nodes(_, ints_nil);

    stack_dispose(s); // Dispose should only happen on an empty stack
    return 0;
}
