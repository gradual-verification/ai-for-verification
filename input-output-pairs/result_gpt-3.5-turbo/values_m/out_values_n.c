#include "verifast.h"

struct node
{
    struct node *next;
    int value;
};

struct stack
{
    struct node *head;
};

//@ predicate nodes(struct node *node) =
//@   node == 0 ? true : node->next |-> ?next &*& node->value |-> ?value &*& malloc_block_node(node) &*& nodes(next);

//@ predicate stack(struct stack *stack; struct node *head) =
//@   stack->head |-> head &*& malloc_block_stack(stack) &*& nodes(head);

//@ fixpoint nodes_count(struct node *node) {
//@   switch(node) {
//@     case 0: return 0;
//@     case n: return 1 + nodes_count(n->next);
//@   }
//@ }

struct stack *create_stack()
    //@ requires true;
    //@ ensures stack(result, 0);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0)
        abort();
    stack->head = 0;
    //@ close nodes(0);
    //@ close stack(stack, 0);
    return stack;
}

void stack_push(struct stack *stack, int value)
    //@ requires stack(stack, ?head) &*& head->next |-> _;
    //@ ensures stack(stack, ?newHead) &*& newHead->next |-> head &*& newHead->value == value;
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
        abort();
    n->next = stack->head;
    n->value = value;
    stack->head = n;
    //@ close nodes(n);
    //@ close stack(stack, n);
}

void stack_dispose(struct stack *stack)
    //@ requires stack(stack, ?head);
    //@ ensures true;
{
    struct node *current = stack->head;
    while (current != 0)
        //@ invariant nodes(current) &*& stack(stack, current);
    {
        struct node *next = current->next;
        free(current);
        current = next;
    }
    free(stack);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct stack *stack = create_stack();
    stack_push(stack, 42);
    stack_dispose(stack);
    return 0;
}
