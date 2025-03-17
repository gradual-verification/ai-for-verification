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


/*@

fixpoint ints ints_append(ints values1, ints values2) {
    switch (values1) {
        case ints_nil: return values2;
        case ints_cons(h, t): return ints_cons(h, ints_append(t, values2));
    }
}


fixpoint ints ints_reverse(ints values) {
    switch (values) {
        case ints_nil: return ints_nil;
        case ints_cons(h, t): return ints_append(ints_reverse(t), ints_cons(h, ints_nil));
    }
}

@*/

void stack_reverse(struct stack *stack)
    //@ requires stack(stack, ?values);
    //@ ensures stack(stack, ints_reverse(values));
{
    struct node *n = stack->head;
    struct node *m = 0;
    while (n != 0)
    {
        struct node *next = n->next;
        n->next = m;
        m = n;
        n = next;
    }
    stack->head = m;
}