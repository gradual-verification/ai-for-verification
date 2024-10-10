#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

/*@
predicate nodes(struct node *node, int count) =
    node == 0 ?
        count == 0
    :
        node->value |-> ?v &*& node->next |-> ?next &*& nodes(next, count - 1);

predicate stack(struct stack *stack, int count) =
    stack->head |-> ?h &*& nodes(h, count);
@*/

struct stack {
    struct node *head;
};

struct stack *create_stack()
//@ requires true;
//@ ensures stack(result, 0);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0) { abort(); }
    stack->head = 0;
    return stack;
}

void stack_push(struct stack *stack, int value)
//@ requires stack(stack, ?count);
//@ ensures stack(stack, count + 1);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) { abort(); }
    n->value = value;
    n->next = stack->head;
    stack->head = n;
}

int stack_pop(struct stack *stack)
//@ requires stack(stack, ?count) &*& 0 < count;
//@ ensures stack(stack, count - 1);
{
    struct node *head = stack->head;
    int result = head->value;
    stack->head = head->next;
    free(head);
    return result;
}

typedef bool int_predicate(int x);
//@ requires true;
//@ ensures true;

struct node *nodes_filter(struct node *n, int_predicate *p)
//@ requires nodes(n, ?count) &*& is_int_predicate(p) == true;
//@ ensures nodes(result, ?newCount) &*& newCount <= count;
{
    if (n == 0) {
        return 0;
    } else {
        bool keep = p(n->value);
        if (keep) {
            struct node *next = nodes_filter(n->next, p);
            n->next = next;
            return n;
        } else {
            struct node *next = n->next;
            free(n);
            return nodes_filter(next, p);
        }
    }
}

void stack_filter(struct stack *stack, int_predicate *p)
//@ requires stack(stack, ?count) &*& is_int_predicate(p) == true;
//@ ensures stack(stack, ?newCount) &*& newCount <= count;
{
    struct node *head = nodes_filter(stack->head, p);
    stack->head = head;
}

void nodes_dispose(struct node *n)
//@ requires nodes(n, _);
//@ ensures true;
{
    if (n != 0) {
        nodes_dispose(n->next);
        free(n);
    }
}

void stack_dispose(struct stack *stack)
//@ requires stack(stack, _);
//@ ensures true;
{
    nodes_dispose(stack->head);
    free(stack);
}

bool neq_20(int x) //@ : int_predicate
//@ requires true;
//@ ensures true;
{
    return x != 20;
}

int main()
//@ requires true;
//@ ensures true;
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    stack_push(s, 30);
    stack_filter(s, neq_20);
    stack_dispose(s);
    return 0;
}
