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

lemma void ints_append_nil_lemma(ints values)
    requires true;
    ensures ints_append(values, ints_nil) == values;
{
    switch (values) {
        case ints_nil:
        case ints_cons(h, t):
            ints_append_nil_lemma(t);
    }
}

lemma void ints_append_assoc_lemma(ints values1, ints values2, ints values3)
    requires true;
    ensures ints_append(ints_append(values1, values2), values3) == ints_append(values1, ints_append(values2, values3));
{
    switch (values1) {
        case ints_nil:
        case ints_cons(h, t):
            ints_append_assoc_lemma(t, values2, values3);
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
    //@ open stack(stack, values);
    struct node *n = stack->head;
    struct node *m = 0;
    //@ close nodes(m, ints_nil);
    //@ ints_append_nil_lemma(ints_reverse(values));
    while (n != 0)
        //@ invariant nodes(m, ?values1) &*& nodes(n, ?values2) &*& ints_reverse(values) == ints_append(ints_reverse(values2), values1);
    {
        //@ open nodes(n, values2);
        struct node *next = n->next;
        //@ assert nodes(next, ?values2tail) &*& n->value |-> ?value;
        n->next = m;
        m = n;
        n = next;
        //@ close nodes(m, ints_cons(value, values1));
        //@ ints_append_assoc_lemma(ints_reverse(values2tail), ints_cons(value, ints_nil), values1);
    }
    //@ open nodes(n, _);
    stack->head = m;
    //@ close stack(stack, ints_reverse(values));
}