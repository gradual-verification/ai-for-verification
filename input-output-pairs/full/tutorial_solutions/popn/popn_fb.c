#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

struct stack {
    struct node *head;
};

/*@

predicate nodes(struct node *node, int count) =
    node == 0 ? count == 0 : 0 < count &*& node->next |-> ?next &*& node->value |-> ?value &*& nodes(next, count - 1);

predicate stack(struct stack *stack, int count) =
    stack->head |-> ?head &*& 0 <= count &*& nodes(head, count);

@*/

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

void stack_popn(struct stack *stack, int n)
    //@ requires stack(stack, ?count) &*& 0 <= n &*& n <= count;
    //@ ensures stack(stack, count - n);
{
    int i = 0;
    while (i < n)
    {
        stack_pop(stack);
        i++;
    }
}