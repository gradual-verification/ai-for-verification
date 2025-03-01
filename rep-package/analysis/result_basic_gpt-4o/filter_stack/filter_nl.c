#include "stdlib.h"
/* @ #include "predicates.gh" @*/

// Define a linked list predicate for stack and node
/*@
predicate nodes(struct node *n;) =
    n == 0 ?
        emp
    :
        malloc_block_node(n) &*& n->next |-> ?next &*& n->value |-> ?value &*& nodes(next);

predicate stack(struct stack *stack;) =
    malloc_block_stack(stack) &*& stack->head |-> ?head &*& nodes(head);
@*/

struct node
{
    struct node *next;
    int value;
};

struct stack
{
    struct node *head;
};


struct stack *create_stack()
//@ requires true;
//@ ensures stack(result);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0)
    {
        abort();
    }
    stack->head = 0;
    return stack;
}


void stack_push(struct stack *stack, int value)
//@ requires stack(stack);
//@ ensures stack(stack);
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


int stack_pop(struct stack *stack)
//@ requires stack(stack) &*& stack->head |-> ?hd &*& hd != 0 &*& nodes(hd);
//@ ensures stack(stack) &*& result == hd->value;
{
    struct node *head = stack->head;
    int result = head->value;
    stack->head = head->next;
    free(head);
    return result;
}

typedef bool int_predicate(int x);
//@ requires true;
//@ ensures true;

/*@
predicate int_predicate(int_predicate *p) = true;
@*/


struct node *nodes_filter(struct node *n, int_predicate *p)
//@ requires nodes(n) &*& is_int_predicate(p) == true;
//@ ensures nodes(result);
{
    if (n == 0)
    {
        return 0;
    }
    else
    {
        bool keep = p(n->value);
        if (keep)
        {
            struct node *next = nodes_filter(n->next, p);
            n->next = next;
            return n;
        }
        else
        {
            struct node *next = n->next;
            free(n);
            struct node *result = nodes_filter(next, p);
            return result;
        }
    }
}


void stack_filter(struct stack *stack, int_predicate *p)
//@ requires stack(stack) &*& is_int_predicate(p) == true;
//@ ensures stack(stack);
{
    struct node *head = nodes_filter(stack->head, p);
    stack->head = head;
}


void nodes_dispose(struct node *n)
//@ requires nodes(n);
//@ ensures emp;
{
    if (n != 0)
    {
        nodes_dispose(n->next);
        free(n);
    }
}


void stack_dispose(struct stack *stack)
//@ requires stack(stack);
//@ ensures emp;
{
    nodes_dispose(stack->head);
    free(stack);
}


bool neq_20(int x) //@ : int_predicate
//@ requires true;
//@ ensures true;
{
    return x != 20;
}


int main()
//@ requires true;
//@ ensures true;
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    stack_push(s, 30);
    stack_filter(s, neq_20);
    stack_dispose(s);
    return 0;
}
