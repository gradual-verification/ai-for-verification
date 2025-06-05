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

fixpoint int ints_head(ints values) {
    switch (values) {
        case ints_nil: return 0;
        case ints_cons(value, values0): return value;
    }
}

fixpoint ints ints_tail(ints values) {
    switch (values) {
        case ints_nil: return ints_nil;
        case ints_cons(value, values0): return values0;
    }
}

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

struct stack *create_stack()
    //@ requires true;
    //@ ensures stack(result, ints_nil);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0) { abort(); }
    stack->head = 0;
    return stack;
}

void stack_push(struct stack *stack, int value)
    //@ requires stack(stack, ?values);
    //@ ensures stack(stack, ints_cons(value, values));
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) { abort(); }
    n->next = stack->head;
    n->value = value;
    stack->head = n;
}

int stack_pop(struct stack *stack)
    //@ requires stack(stack, ?values) &*& values != ints_nil;
    //@ ensures stack(stack, ints_tail(values)) &*& result == ints_head(values);
{
    struct node *head = stack->head;
    int result = head->value;
    stack->head = head->next;
    free(head);
    return result;
}

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

void stack_dispose(struct stack *s)
  //@ requires stack(s, ?vs);
  //@ ensures true;
{
  struct node* n = s->head;
  while(n != 0) 
  {
    struct node* tmp = n;
    n = n->next;
    free(tmp);
  }
  free(s);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    int result1 = stack_pop(s);
    assert(result1 == 20);
    int result2 = stack_pop(s);
    assert(result2 == 10);
    stack_dispose(s);
    return 0;
}
