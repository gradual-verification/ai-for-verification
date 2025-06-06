
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
        node->next |-> ?next &*& node->value |-> ?value &*& value >= 0 &*& malloc_block_node(node) &*&
        nodes(next, ?values0) &*& values == ints_cons(value, values0);

predicate stack(struct stack *stack, ints values) =
    stack->head |-> ?head &*& malloc_block_stack(stack) &*& nodes(head, values);

@*/

/*@

fixpoint int ints_sum(ints values) {
    switch (values) {
        case ints_nil: return 0;
        case ints_cons(value, values0): return value + ints_sum(values0);
    }
}

@*/

int nodes_get_sum(struct node *node)
    //@ requires nodes(node, ?values) &*& ints_sum(values) <= INT_MAX;
    //@ ensures nodes(node, values) &*& result == ints_sum(values);
{
    //@ open nodes(node, values);
    int result = 0;
    if (node != 0) {
        int tailSum = nodes_get_sum(node->next);
        result = node->value + tailSum;
    }
    //@ close nodes(node, values);
    return result;
}

int stack_get_sum(struct stack *stack)
    //@ requires stack(stack, ?values) &*& ints_sum(values) <= INT_MAX;
    //@ ensures stack(stack, values) &*& result == ints_sum(values);
{
    //@ open stack(stack, values);
    int result = nodes_get_sum(stack->head);
    //@ close stack(stack, values);
    return result;
}