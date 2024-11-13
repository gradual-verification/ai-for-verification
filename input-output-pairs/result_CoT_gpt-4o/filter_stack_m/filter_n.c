#include "stdlib.h"
#include "stdbool.h"

/*@
predicate nodes(struct node* head) =
    head == 0 ? emp :
    malloc_block_node(head) &*& nodes(head->next);

predicate stack(struct stack *stack) =
    malloc_block_stack(stack) &*& nodes(stack->head);

predicate int_predicate(int_predicate *p;);
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

/*@
requires true;
ensures stack(result) &*& result != 0;
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
requires stack(stack) &*& int_predicate(p) &*& stack != 0;
ensures stack(stack);
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
requires stack(stack) &*& stack != 0 &*& stack->head != 0;
ensures stack(stack);
@*/
int stack_pop(struct stack *stack)
{
    struct node *head = stack->head;
    int result = head->value;
    stack->head = head->next;
    free(head);
    return result;
}

/*@
requires nodes(n) &*& int_predicate(p);
ensures nodes(result);
@*/
struct node *nodes_filter(struct node *n, int_predicate *p)
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

/*@
requires stack(stack) &*& int_predicate(p) &*& stack != 0;
ensures stack(stack);
@*/
void stack_filter(struct stack *stack, int_predicate *p)
{
    struct node *head = nodes_filter(stack->head, p);
    stack->head = head;
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
requires stack(stack) &*& stack != 0;
ensures emp;
@*/
void stack_dispose(struct stack *stack)
{
    nodes_dispose(stack->head);
    free(stack);
}

/*@
requires true;
ensures  \result == ! (x == 20);
@*/
bool neq_20(int x) //@ : int_predicate
{
    return x != 20;
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
    stack_push(s, 30);
    stack_filter(s, neq_20);
    stack_dispose(s);
    return 0;
}
