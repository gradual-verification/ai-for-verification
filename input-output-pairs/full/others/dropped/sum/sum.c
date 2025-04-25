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
    node == 0 ? count == 0 : 0 < count &*& node->next |-> ?next &*& node->value |-> ?value &*& value >= 0 &*& malloc_block_node(node) &*& nodes(next, count - 1);

predicate stack(struct stack *stack, int count) =
    stack->head |-> ?head &*& malloc_block_stack(stack) &*& 0 <= count &*& nodes(head, count);

@*/

int nodes_get_sum(struct node *nodes)
    //@ requires nodes(nodes, ?count);
    //@ ensures nodes(nodes, count);
{
    int result = 0;
    //@ open nodes(nodes, count);
    if (nodes != 0) {
        result = nodes_get_sum(nodes->next);
        if (result > INT_MAX - nodes->value)
            abort();
        result += nodes->value;
    }
    //@ close nodes(nodes, count);
    return result;
}

int stack_get_sum(struct stack *stack)
    //@ requires stack(stack, ?count);
    //@ ensures stack(stack, count);
{
    //@ open stack(stack, count);
    int result = nodes_get_sum(stack->head);
    //@ close stack(stack, count);
    return result;
}

void stack_dispose(struct stack *stack)
    //@ requires stack(stack, _);
    //@ ensures true;
{
    //@ open stack(stack, _);
    struct node *n = stack->head;
    while (n != 0)
        //@ invariant nodes(n, _);
    {
        //@ open nodes(n, _);
        struct node *next = n->next;
        free(n);
        n = next;
    }
    //@ open nodes(0, _);
    free(stack);
}
