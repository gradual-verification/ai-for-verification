```c
#include "stdlib.h"

struct node
{
    struct node *next;
    int value;
};

/*@
inductive ints = ints_nil | ints_cons(int, ints);

predicate nodes(struct node *node, ints values) =
    node == 0 ?
        values == ints_nil
    :
        node->next |-> ?next &*& node->value |-> ?value &*&
        nodes(next, ?values0) &*& values == ints_cons(value, values0);
@*/

struct stack
{
    struct node *head;
};
/*@

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
    stack->head = n;
    //@ close nodes(n, ints_cons(value, values));
    //@ close stack(stack, ints_cons(value, values));
}

int stack_pop(struct stack *stack)
//@ requires stack(stack, ints_cons(?value, ?values0));
//@ ensures stack(stack, values0) &*& result == value;
{
    //@ open stack(stack, ints_cons(value, values0));
    struct node *head = stack->head;
    //@ open nodes(head, ints_cons(value, values0));
    int value = head->value;
    stack->head = head->next;
    //@ close nodes(stack->head, values0);
    //@ close stack(stack, values0);
    free(head);
    return value;
}

void nodes_dispose(struct node *node)
//@ requires nodes(node, _);
//@ ensures emp;
{
    //@ open nodes(node, _);
    if (node == 0) {
        //@ close emp;
    } else {
        struct node *next = node->next;
        nodes_dispose(next);
        free(node);
    }
}

void stack_dispose(struct stack *stack)
//@ requires stack(stack, _);
//@ ensures emp;
{
    //@ open stack(stack, _);
    nodes_dispose(stack->head);
    free(stack);
    //@ close emp;
}

int main()
//@ requires true;
//@ ensures true;
{
    struct stack *stack = create_stack();
    stack_push(stack, 1);
    stack_push(stack, 2);
    stack_push(stack, 3);
    int x = stack_pop(stack);
    stack_dispose(stack);
    return 0;
}
```
