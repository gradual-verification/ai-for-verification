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
    //@ close nodes(0, ints_nil);
    //@ close stack(stack, ints_nil);
}

void stack_push(struct stack *stack, int value)
//@ requires stack(stack, ?values);
//@ ensures stack(stack, ints_cons(value, values));
{
    //@ open stack(stack, values);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->next = stack->head;
    n->value = value;
    stack->head = n;
    //@ close nodes(n, ints_cons(value, values));
    //@ close stack(stack, ints_cons(value, values));
}

int stack_pop(struct stack *stack)
//@ requires stack(stack, ints_cons(?val, ?values0));
//@ ensures stack(stack, values0) &*& result == val;
{
    //@ open stack(stack, ints_cons(val, values0));
    struct node *head = stack->head;
    //@ open nodes(head, _);
    int value = head->value;
    stack->head = head->next;
    free(head);
    return value;
    //@ close stack(stack, values0);
}

void stack_dispose(struct stack *stack)
//@ requires stack(stack, ints_nil);
//@ ensures true;
{
    //@ open stack(stack, ints_nil);
    //@ open nodes(_, _);
    free(stack);
}

int main()
//@ requires true;
//@ ensures true;
{
    struct stack *s = create_stack();
    stack_push(s, 42);
    int v = stack_pop(s);
    stack_dispose(s);
    return 0;
}
