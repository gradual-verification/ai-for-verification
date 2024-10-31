```c
#include "stdlib.h"

struct node
{
    struct node *next;
    int value;
};

struct stack
{
    struct node *head;
};

/*@
predicate nodes(struct node *node, int count) =
    node == 0 ? 
        count == 0 
    :
        node->next |-> ?next &*& node->value |-> _ &*& malloc_block_node(node) &*& nodes(next, ?next_count) &*& count == next_count + 1;

predicate stack(struct stack *stack, int count) =
    stack->head |-> ?head &*& malloc_block_stack(stack) &*& nodes(head, count);
@*/

struct stack *create_stack()
//@ requires true;
//@ ensures stack(result, 0);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0)
    {
        abort();
    }
    //@ malloc_block_stack(stack);
    stack->head = 0;
    //@ close nodes(0, 0);
    //@ close stack(stack, 0);
    return stack;
}

void stack_push(struct stack *stack, int value)
//@ requires stack(stack, ?count);
//@ ensures stack(stack, count + 1);
{
    //@ open stack(stack, count);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    //@ malloc_block_node(n);
    n->next = stack->head;
    n->value = value;
    stack->head = n;
    //@ close nodes(n, count + 1);
    //@ close stack(stack, count + 1);
}

void stack_pop(struct stack *stack)
//@ requires stack(stack, ?count) &*& 0 < count;
//@ ensures stack(stack, count - 1);
{
    //@ open stack(stack, count);
    //@ open nodes(stack->head, ?next_count);
    struct node *head = stack->head;
    int result = head->value;
    stack->head = head->next;
    //@ close nodes(stack->head, count - 1);
    //@ close stack(stack, count - 1);
    free(head);
}

void nodes_dispose(struct node *n)
//@ requires nodes(n, _);
//@ ensures true;
{
    if (n != 0)
    {
        //@ open nodes(n, _);
        nodes_dispose(n->next);
        free(n);
    }
    else
    {
        //@ open nodes(0, _);
    }
}

void stack_dispose(struct stack *stack)
//@ requires stack(stack, _);
//@ ensures true;
{
    //@ open stack(stack, _);
    nodes_dispose(stack->head);
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
```
