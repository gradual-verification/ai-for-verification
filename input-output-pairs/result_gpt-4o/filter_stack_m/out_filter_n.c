#include "stdlib.h"
#include "verifast.h"

struct node
{
    struct node *next;
    int value;
};

/*@
predicate nodes(struct node* n, list<int> vs) =
    n == 0 ? vs == nil : 
    n->value |-> ?v &*& n->next |-> ?next &*& 
    nodes(next, ?rest) &*& vs == cons(v, rest);

predicate stack(struct stack* s, list<int> vs) =
    s->head |-> ?head &*& nodes(head, vs);
@*/

struct stack
{
    struct node *head;
};

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
requires stack(stack, ?vs) &*& vs != nil;
ensures stack(stack, tail(vs)) &*& result == head(vs);
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
predicate nodes_disposed(struct node* n) = 
    n == 0 ? true : n->next |-> ?next &*& free_block(n) &*& nodes_disposed(next);

lemma void nodes_dispose(struct node *n) 
    requires nodes(n, ?vs);
    ensures nodes_disposed(n);
{
    if (n != 0)
    {
        nodes_dispose(n->next);
        free(n);
    }
}
@*/

/*@
requires stack(stack, ?vs);
ensures emp;
@*/
void stack_dispose(struct stack *stack)
{
    nodes_dispose(stack->head);
    free(stack);
}

typedef bool int_predicate(int x);

/*@
predicate predicate_neq_20() = emp;

fixpoint bool neq_20_fp(int x) {
    return x != 20;
}
@*/

bool neq_20(int x) //@ : int_predicate
/*@ requires predicate_neq_20(); ensures predicate_neq_20() &*& result == neq_20_fp(x); @*/
{
    return x != 20;
}

/*@
requires stack(stack, ?vs) &*& is_int_predicate(p) == true;
ensures stack(stack, filter(predicate_indicator(p), vs));
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
requires stack(stack, ?vs) &*& is_int_predicate(p) == true;
ensures stack(stack, filter(predicate_indicator(p), vs));
@*/
void stack_filter(struct stack *stack, int_predicate *p)
{
    struct node *head = nodes_filter(stack->head, p);
    stack->head = head;
}

int main()
/*@
requires true;
ensures true;
@*/
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    stack_push(s, 30);
    stack_filter(s, neq_20);
    stack_dispose(s);
    return 0;
}
