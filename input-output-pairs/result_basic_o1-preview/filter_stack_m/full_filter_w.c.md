```c
#include "stdlib.h"

struct node
{
    struct node *next;
    int value;
};

/*@
predicate nodes(struct node *node, int count) =
    node == 0 ?
        count == 0
    :
        0 < count &*& node->next |-> ?next &*& node->value |-> ?value &*&
        nodes(next, count - 1);

predicate stack(struct stack *stack, int count) =
    stack->head |-> ?head &*& nodes(head, count);
@*/

struct stack
{
    struct node *head;
};

struct stack *create_stack()
    //@ requires true;
    //@ ensures stack(result, 0);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0)
    {
        abort();
    }
    stack->head = 0;
    //@ close stack(stack, 0);
    return stack;
}

void stack_push(struct stack *stack, int value)
    //@ requires stack(stack, ?count);
    //@ ensures stack(stack, count + 1);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    n->next = stack->head;
    n->value = value;
    //@ open stack(stack, count);
    //@ close nodes(n, count + 1);
    stack->head = n;
    //@ close stack(stack, count + 1);
}

int stack_pop(struct stack *stack)
    //@ requires stack(stack, ?count) &*& 0 < count;
    //@ ensures stack(stack, count - 1);
{
    //@ open stack(stack, count);
    struct node *head = stack->head;
    //@ open nodes(head, count);
    int result = head->value;
    stack->head = head->next;
    free(head);
    //@ close nodes(stack->head, count - 1);
    //@ close stack(stack, count - 1);
    return result;
}

/*@

typedef bool int_predicate(int x);
    //@ requires true;
    //@ ensures true;

predicate is_int_predicate(int_predicate *p) =
    [_]function_pointer(p, int_predicate);

@*/

struct node *nodes_filter(struct node *n, int_predicate *p)
    //@ requires nodes(n, ?count) &*& is_int_predicate(p);
    //@ ensures nodes(result, ?new_count);
{
    if (n == 0)
    {
        //@ close nodes(0, 0);
        return 0;
    }
    else
    {
        //@ open nodes(n, count);
        bool keep = p(n->value);
        if (keep)
        {
            struct node *next = nodes_filter(n->next, p);
            n->next = next;
            //@ close nodes(n, _);
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
    //@ requires stack(stack, ?count) &*& is_int_predicate(p);
    //@ ensures stack(stack, ?new_count);
{
    //@ open stack(stack, count);
    struct node *head = nodes_filter(stack->head, p);
    stack->head = head;
    //@ close stack(stack, _);
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
}

void stack_dispose(struct stack *stack)
    //@ requires stack(stack, _);
    //@ ensures true;
{
    //@ open stack(stack, _);
    nodes_dispose(stack->head);
    free(stack);
}

bool neq_20(int x)
    //@ : int_predicate
    //@ requires true;
    //@ ensures true;
{
    return x != 20;
}

int main()
    //@ requires true;
    //@ ensures true;
{
    //@ close is_int_predicate(neq_20);
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    stack_push(s, 30);
    stack_filter(s, neq_20);
    stack_dispose(s);
    return 0;
}
```
