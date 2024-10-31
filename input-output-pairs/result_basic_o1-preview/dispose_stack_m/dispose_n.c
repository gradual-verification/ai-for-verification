#include "stdlib.h"
#include "stddef.h"
//@ #include "listex.gh"

struct node
{
    struct node *next;
    int value;
};

struct stack
{
    struct node *head;
};

//@ predicate nodes(struct node *n, list<int> vs) =
//@     n == 0 ? vs == nil :
//@     n->next |-> ?next &*& n->value |-> ?v &*& malloc_block_node(n) &*& nodes(next, ?rest_vs) &*& vs == cons(v, rest_vs);

//@ predicate stack(struct stack *s, list<int> vs) =
//@     s->head |-> ?head &*& nodes(head, vs) &*& malloc_block_stack(s);

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
    //@ close nodes(0, nil);
    //@ close stack(stack, nil);
    return stack;
}

void stack_push(struct stack *stack, int value)
    //@ requires stack(stack, ?vs);
    //@ ensures stack(stack, cons(value, vs));
{
    //@ open stack(stack, vs);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    n->next = stack->head;
    n->value = value;
    //@ close nodes(n, cons(value, vs));
    stack->head = n;
    //@ close stack(stack, cons(value, vs));
}

void stack_pop(struct stack *stack)
    //@ requires stack(stack, ?vs) &*& vs != nil;
    //@ ensures stack(stack, tail(vs));
{
    //@ open stack(stack, vs);
    //@ open nodes(stack->head, vs);
    struct node *head = stack->head;
    int result = head->value;
    stack->head = head->next;
    //@ head->next == ?next;
    //@ head->value == head->value;
    //@ malloc_block_node(head);
    free(head);
    //@ close nodes(stack->head, tail(vs));
    //@ close stack(stack, tail(vs));
}

void nodes_dispose(struct node *n)
    //@ requires nodes(n, _);
    //@ ensures true;
{
    //@ open nodes(n, _);
    if (n != 0)
    {
        struct node *next = n->next;
        nodes_dispose(next);
        //@ n->value |-> _;
        //@ malloc_block_node(n);
        free(n);
    }
    else
    {
        //@ assert n == 0;
    }
}

void stack_dispose(struct stack *stack)
    //@ requires stack(stack, _);
    //@ ensures true;
{
    //@ open stack(stack, _);
    nodes_dispose(stack->head);
    //@ malloc_block_stack(stack);
    free(stack);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    stack_pop(s);
    stack_pop(s);
    stack_dispose(s);
    return 0;
}
