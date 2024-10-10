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

//@predicate valid_node(struct node *n) = n == 0 || (\valid(n) && \valid(n->next) && valid_node(n->next));

//@predicate valid_stack(struct stack *s) = \valid(s) && (s->head == 0 || valid_node(s->head));

//@predicate stack_contains_no_null(struct stack *s, struct node *n) = valid_stack(s) && n == 0 || (n != 0 && stack_contains_no_null(s, n->next));

//@predicate node_contains_no_null(struct node *n) = n == 0 || (n != 0 && node_contains_no_null(n->next));

//@predicate nodes_properly_linked(struct node *n) = n == 0 || (valid_node(n) && nodes_properly_linked(n->next) && (\at(n, L) != 0 ==> \at(n, L)->next == n));

//@predicate stack_contains_all_nodes(struct stack *s, struct node *n) = valid_stack(s) && n == 0 || (n != 0 && stack_contains_all_nodes(s, n->next));

//@predicate node_distinct_values(struct node *n, int x) = n == 0 || (n != 0 && node_distinct_values(n->next, x) && n->value != x);

struct stack *create_stack()
//@requires true
//@ensures \result != 0 && valid_stack(\result) && stack_contains_no_null(\result, \result->head)
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0)
    {
        abort();
    }
    stack->head = 0;
    //@close valid_stack(stack);
    //@close stack_contains_no_null(stack, stack->head);
    return stack;
}
 
void stack_push(struct stack *stack, int value)
//@requires valid_stack(stack)
//@ensures valid_stack(stack) && stack_contains_no_null(stack, stack->head) && stack_contains_all_nodes(stack, stack->head) && node_distinct_values(stack->head, value) && stack_contains_no_null(stack, stack->head)
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    n->next = stack->head;
    n->value = value;
    stack->head = n;
    //@close valid_stack(stack);
    //@close stack_contains_no_null(stack, stack->head);
    //@close stack_contains_all_nodes(stack, stack->head);
    //@close node_distinct_values(stack->head, value);
    //@close stack_contains_no_null(stack, stack->head);
}

int stack_pop(struct stack *stack)
//@requires valid_stack(stack) && stack_contains_no_null(stack, stack->head)
//@ensures valid_stack(stack) && stack_contains_all_nodes(stack, stack->head) && \result != 0 && !node_distinct_values(stack->head, \result) && stack_contains_no_null(stack, stack->head)
{
    struct node *head = stack->head;
    int result = head->value;
    stack->head = head->next;
    free(head);
    //@close valid_stack(stack);
    //@close stack_contains_all_nodes(stack, stack->head);
    //@close !node_distinct_values(stack->head, result);
    //@close stack_contains_no_null(stack, stack->head);
    return result;
}

struct node *nodes_filter(struct node *n, int_predicate *p)
//@requires node_contains_no_null(n)
//@ensures node_contains_no_null(\result)
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
//@requires valid_stack(stack)
//@ensures valid_stack(stack) && stack_contains_no_null(stack, stack->head) && stack_contains_all_nodes(stack, stack->head)
{
    struct node *head = nodes_filter(stack->head, p);
    stack->head = head;
    //@close valid_stack(stack);
    //@close stack_contains_no_null(stack, stack->head);
    //@close stack_contains_all_nodes(stack, stack->head);
}

void nodes_dispose(struct node *n)
//@requires node_contains_no_null(n)
//@ensures true
{
    if (n != 0)
    {
        nodes_dispose(n->next);
        free(n);
    }
}

void stack_dispose(struct stack *stack)
//@requires valid_stack(stack)
//@ensures true
{
    nodes_dispose(stack->head);
    free(stack);
}

bool neq_20(int x) //@ : int_predicate
//@requires true
//@ensures \result <==> x != 20
{
    return x != 20;
}

int main()
//@requires true
//@ensures true
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    stack_push(s, 30);
    stack_filter(s, neq_20);
    stack_dispose(s);
    return 0;
}
