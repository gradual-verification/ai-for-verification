#include "stdlib.h"
#include "stdbool.h"

struct node
{
    struct node *next;
    int value;
};

// Predicate to describe a linked list starting from 'head'
/*@
predicate nodes(struct node* head, list<int> values) =
    head == 0 ?
        values == nil
    :
        head->next |-> ?next &*& head->value |-> ?v &*& malloc_block_node(head) &*&
        nodes(next, ?vs) &*& values == cons(v, vs);
@*/

struct stack
{
    struct node *head;
};

/*@
predicate stack(struct stack *s; list<int> values) =
    s->head |-> ?h &*& malloc_block_stack(s) &*& nodes(h, values);
@*/

/*@
  requires true;
  ensures stack(result, nil);
@*/
struct stack *create_stack()
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0)
    {
        abort();
    }
    stack->head = 0;
    return stack;
}

/*@
  requires stack(stack, ?vs);
  ensures stack(stack, cons(value, vs));
@*/
void stack_push(struct stack *stack, int value)
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

/*@
  requires stack(stack, cons(?v, ?vs));
  ensures stack(stack, vs);
@*/
void stack_pop(struct stack *stack)
{
    struct node *head = stack->head;
    int result = head->value;
    stack->head = head->next;
    free(head);
}

/*@
  requires nodes(n, ?vs);
  ensures true;
@*/
void nodes_dispose(struct node *n)
{
    if (n != 0)
    {
        struct node *next = n->next;
        free(n);
        nodes_dispose(next);
    }
}

/*@
  requires stack(stack, ?vs);
  ensures true;
@*/
void stack_dispose(struct stack *stack)
{
    nodes_dispose(stack->head);
    free(stack);
}

/*@
  requires true;
  ensures true;
@*/
int main()
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    stack_pop(s);
    stack_pop(s);
    stack_dispose(s);
    return 0;
}
