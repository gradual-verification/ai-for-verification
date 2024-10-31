```c
#include "stdlib.h"

struct node
{
    struct node *next;
    int value;
};

/*@
predicate nodes(struct node *node) =
    node == 0 ?
        emp
    :
        node->next |-> ?next &*& node->value |-> _ &*& malloc_block_node(node) &*&
        nodes(next);

predicate stack(struct stack *stack) =
    stack->head |-> ?head &*& malloc_block_stack(stack) &*& nodes(head);
@*/

struct stack
{
    struct node *head;
};

struct stack *create_stack()
//@ requires emp;
//@ ensures stack(result);
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
//@ requires stack(stack);
//@ ensures stack(stack);
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

int stack_pop(struct stack *stack)
//@ requires stack(stack) &*& stack->head != 0;
//@ ensures stack(stack);
{
    struct node *head = stack->head;
    int result = head->value;
    stack->head = head->next;
    free(head);
    return result;
}

/*@
fixpoint bool neq_20_fp(int x) { return x != 20; }

typedef bool int_predicate(int x) //@ : int_predicate_t;

/*@
predicate int_predicate_t(int_predicate *p; fixpoint(int, bool) fp) =
    p == neq_20 &*& fp == neq_20_fp;

@*/

bool neq_20(int x) //@ : int_predicate_t(neq_20_fp)
//@ requires emp;
//@ ensures result == neq_20_fp(x);
{
    return x != 20;
}

struct node *nodes_filter(struct node *n, int_predicate *p)
//@ requires nodes(n) &*& int_predicate_t(p, ?fp);
//@ ensures nodes(result);
{
    if (n == 0)
    {
        return 0;
    }
    else
    {
        bool keep = p(n->value);
        //@ assert keep == fp(n->value);
        if (keep)
        {
            struct node *next = nodes_filter(n->next, p);
            n->next = next;
            return n;
        }
        else
        {
            struct node *next = n->next;
            free(n);
            return nodes_filter(next, p);
        }
    }
}

void stack_filter(struct stack *stack, int_predicate *p)
//@ requires stack(stack) &*& int_predicate_t(p, _);
//@ ensures stack(stack);
{
    stack->head = nodes_filter(stack->head, p);
}

void nodes_dispose(struct node *n)
//@ requires nodes(n);
//@ ensures emp;
{
    if (n != 0)
    {
        struct node *next = n->next;
        nodes_dispose(next);
        free(n);
    }
}

void stack_dispose(struct stack *stack)
//@ requires stack(stack);
//@ ensures emp;
{
    nodes_dispose(stack->head);
    free(stack);
}

int main()
//@ requires emp;
//@ ensures emp;
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    stack_push(s, 30);
    stack_filter(s, neq_20);
    stack_dispose(s);
    return 0;
}
```
