#include "stdlib.h"

/*@
predicate stack(struct stack *stack, predicate(struct node *) nodes) =
    stack->head |-> ?head &*& nodes(head);

predicate nodes(struct node *n;) =
    n == 0 ?
        emp
    :
        n->value |-> _ &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next);
@*/

struct stack {
    struct node *head;
};

struct node {
    struct node *next;
    int value;
};

/*@
requires true;
ensures result != 0 &*& stack(result, nodes) &*& malloc_block_stack(result);
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
requires stack(stack, nodes);
ensures stack(stack, nodes) &*& malloc_block_node(?n) &*& nodes(stack->head) == n &*& n->value |-> value &*& n->next |-> ?next &*& nodes(next);
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
requires stack(stack, nodes) &*& stack->head != 0;
ensures stack(stack, nodes);
@*/
void stack_pop(struct stack *stack)
{
    struct node *head = stack->head;
    int result = head->value;
    stack->head = head->next;
    free(head);
}

/*@
requires nodes(n);
ensures emp;
@*/
void nodes_dispose(struct node *n) 
{
    if (n != 0) 
    {
        nodes_dispose(n->next);
        free(n);
    }
}

/*@
requires stack(stack, nodes);
ensures emp;
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
