#include "stdlib.h"
#include "stdbool.h"

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
0 < count &*& node->next |-> ?next &*& node->value |-> ?value &*&
malloc_block_node(node) &*& nodes(next, count - 1);

predicate stack(struct stack *stack, int count) =
stack->head |-> ?head &*& malloc_block_stack(stack) &*& 0 <= count &*& nodes(head, count);

//predicate_family int_predicate_pre(int_predicate *p)(int x);
//predicate_family int_predicate_post(int_predicate *p)(int x, bool result);

@*/


/* @
lemma void create_int_predicate()
requires int_predicate_pre(?p)(?x);
ensures int_predicate_post(p)(x, x != 20);
{
    // prove the postcondition of the predicate
}
@ */

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
//@ requires stack(stack, ?count) &*& 0 < count;
//@ ensures stack(stack, count - 1);
{
    //@ open stack(stack, count);
    struct node *head = stack->head;
    //@ open nodes(head, count);
    int result = head->value;
    stack->head = head->next;
    free(head);
    return result;
    //@ close stack(stack, count - 1);
}

struct node *nodes_filter(struct node *n, int_predicate *p)
//@ requires nodes(n, ?count) &*& is_int_predicate(p) == true;
//@ ensures nodes(result, ?new_count) &*& new_count <= count;
{
    if (n == 0)
    {
        return 0;
    }
    else
    {
        //@ open nodes(n, count);
        bool keep = p(n->value);
        // @ close int_predicate_post(p)(n->value, keep);
        if (keep)
        {
            struct node *next = nodes_filter(n->next, p);
            n->next = next;
            //@ open nodes(next, ?cnt);
            //@ close nodes(next, cnt);
            //@ close nodes(n, cnt + 1);
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
//@ requires stack(stack, ?count) &*& is_int_predicate(p) == true;
//@ ensures stack(stack, ?new_count) &*& new_count <= count;
{
    //@ open stack(stack, _);
    struct node *head = nodes_filter(stack->head, p);
    stack->head = head;
    //@ open nodes(head, ?new_count);
    //@ close nodes(head, new_count);
    //@ close stack(stack, new_count);
}

void nodes_dispose(struct node *n)
//@ requires nodes(n, _);
//@ ensures true;
{
    //@ open nodes(n, _);
    if (n != 0)
    {
        
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

// @ predicate_family_instance int_predicate_pre(neq_20)(int x) = true;
// @ predicate_family_instance int_predicate_post(neq_20)(int x, bool result) = true;

typedef bool int_predicate(int x);
//@ requires true;
//@ ensures true;

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
