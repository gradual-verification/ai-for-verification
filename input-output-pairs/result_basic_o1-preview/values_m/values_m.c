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
    //@ close nodes(0, ints_nil);
    //@ close stack(stack, ints_nil);
    return stack;
}

void stack_push(struct stack *stack, int value)
//@ requires stack(stack, ?values);
//@ ensures stack(stack, ints_cons(value, values));
{
    //@ open stack(stack, values);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    n->next = stack->head;
    n->value = value;
    //@ close nodes(n, ints_cons(value, values));
    stack->head = n;
    //@ close stack(stack, ints_cons(value, values));
}

int stack_pop(struct stack *stack)
//@ requires stack(stack, ints_cons(?value, ?values));
//@ ensures stack(stack, values) &*& result == value;
{
    //@ open stack(stack, ints_cons(value, values));
    struct node *head = stack->head;
    //@ open nodes(head, ints_cons(value, values));
    int result = head->value;
    stack->head = head->next;
    //@ close stack(stack, values);
    free(head);
    return result;
}

void nodes_dispose(struct node *node)
//@ requires nodes(node, _);
//@ ensures true;
{
    if (node != 0)
    {
        //@ open nodes(node, _);
        struct node *next = node->next;
        nodes_dispose(next);
        free(node);
    }
    else
    {
        //@ open nodes(0, _);
    }
}

void stack_dispose(struct stack *stack)
//@ requires stack(stack, _);
//@ ensures true;
{
    //@ open stack(stack, _);
    nodes_dispose(stack->head);
    free(stack);
}

int main()
//@ requires true;
//@ ensures true;
{
    struct stack *stack = create_stack();
    stack_push(stack, 10);
    stack_push(stack, 20);
    int a = stack_pop(stack);
    int b = stack_pop(stack);
    stack_dispose(stack);
    return 0;
}
