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
        node->next |-> ?next &*& node->value |-> _ &*&
        malloc_block_node(node) &*& nodes(next, ?next_count) &*&
        count == next_count + 1;

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
    n->next = stack->head;
    n->value = value;
    stack->head = n;
    //@ close nodes(n, count + 1);
    //@ close stack(stack, count + 1);
}

int stack_pop(struct stack *stack)
    //@ requires stack(stack, ?count) &*& count > 0;
    //@ ensures stack(stack, count - 1);
{
    //@ open stack(stack, count);
    //@ open nodes(stack->head, count);
    struct node *head = stack->head;
    int result = head->value;
    stack->head = head->next;
    //@ open nodes(head->next, _);
    //@ free nodes(head, 1);
    free(head);
    //@ close stack(stack, count - 1);
    return result;
}

/*@
typedef bool int_predicate(int x);
    requires true;
    ensures true;

predicate is_int_predicate(int_predicate *p) = true;
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
            //@ new_count = (count - 1) + (next_count);
            //@ close nodes(n, ?total_count);
            return n;
        }
        else
        {
            struct node *next = n->next;
            //@ open nodes(n->next, _);
            free(n);
            struct node *result = nodes_filter(next, p);
            //@ new_count = result_count;
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

bool neq_20(int x) //@ : int_predicate
    //@ requires true;
    //@ ensures true;
{
    return x != 20;
}

/*@

lemma void is_int_predicate_neq_20()
    requires true;
    ensures is_int_predicate(neq_20);
{
}

@*/

int main()
    //@ requires true;
    //@ ensures true;
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    stack_push(s, 30);
    //@ is_int_predicate_neq_20();
    stack_filter(s, neq_20);
    stack_dispose(s);
    return 0;
}
