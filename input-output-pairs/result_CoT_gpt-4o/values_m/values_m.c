#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

struct stack {
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

struct stack *create_stack()
//@ requires true;
//@ ensures stack(result, ints_nil);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0) {
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
    if (n == 0) {
        abort();
    }
    
    n->next = stack->head;
    n->value = value;
    
    //@ open nodes(stack->head, values);
    stack->head = n;
    //@ close nodes(stack->head, ints_cons(value, values));
    //@ close stack(stack, ints_cons(value, values));
}

void stack_dispose(struct stack *stack)
//@ requires stack(stack, ?values);
//@ ensures true;
{
    //@ open stack(stack, values);
    struct node *current = stack->head;
    while (current != 0)
    //@ invariant nodes(current, ?values0);
    {
        //@ open nodes(current, values0);
        struct node *next = current->next;
        free(current);
        current = next;
    }
    free(stack);
}

int main()
//@ requires true;
//@ ensures true;
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    stack_dispose(s);
    return 0;
}
