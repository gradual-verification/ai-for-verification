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
predicate nodes(struct node *n, list<int> l) =
    n == 0 ?
        l == nil
    :
        n->value |-> ?v &*& n->next |-> ?next &*&
        nodes(next, ?rest) &*&
        l == cons(v, rest);

predicate stack(struct stack *s, list<int> l) =
    s->head |-> ?h &*& nodes(h, l);

fixpoint list<int> filter_fp(fixpoint(int, bool) p, list<int> l) {
    switch (l) {
        case nil: return nil;
        case cons(h, t): return p(h) ? cons(h, filter_fp(p, t)) : filter_fp(p, t);
    }
}

predicate_family int_predicate_type(int_predicate *pred)(fixpoint(int, bool) fp);

typedef bool int_predicate(int x);
    //@ requires [_]int_predicate_type(this)(?fp) &*& true;
    //@ ensures [_]int_predicate_type(this)(fp) &*& result == fp(x);

/*@
fixpoint bool neq_20_fp(int x) { return x != 20; }

lemma void neq_20_is_int_predicate()
    requires true;
    ensures int_predicate_type(neq_20)(neq_20_fp);
{
    close int_predicate_type(neq_20)(neq_20_fp);
}
@*/

/***
 * Description:
The create_stack function creates an empty stack.

@return - A pointer to the newly created stack.

This function allocates memory for a new stack and initializes its head to NULL.
If memory allocation fails, the program aborts.
*/
/*@
struct stack *create_stack()
    //@ requires true;
    //@ ensures stack(result, nil);
@*/
struct stack *create_stack()
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0)
    {
        abort();
    }
    stack->head = 0;
    //@ close nodes(0, nil);
    //@ close stack(stack, nil);
    return stack;
}

/***
 * Description:
The stack_push function pushes a value onto the stack.

@param stack - A pointer to the stack.
@param value - The integer value to push onto the stack.

This function allocates a new node, assigns the given value to it,
and sets the new node as the head of the stack.
If memory allocation fails, the program aborts.
*/
/*@
void stack_push(struct stack *stack, int value)
    //@ requires stack(stack, ?l);
    //@ ensures stack(stack, cons(value, l));
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
    //@ close nodes(n, cons(value, l));
    stack->head = n;
    //@ close stack(stack, cons(value, l));
}

/***
 * Description:
The stack_pop function pops a value from the stack.

@param stack - A pointer to the stack.
@return - The integer value popped from the stack.

This function removes the head node from the stack, retrieves its value,
and frees the memory allocated to the head node. The stack must not be empty.
*/
/*@
int stack_pop(struct stack *stack)
    //@ requires stack(stack, cons(?h, ?t));
    //@ ensures stack(stack, t) &*& result == h;
@*/
int stack_pop(struct stack *stack)
{
    //@ open stack(stack, cons(h, t));
    struct node *head = stack->head;
    //@ open nodes(head, cons(h, t));
    int result = head->value;
    stack->head = head->next;
    //@ head->value |-> h;
    //@ head->next |-> ?next;
    //@ close nodes(next, t);
    //@ close stack(stack, t);
    free(head);
    return result;
}

/***
 * Description:
The nodes_filter function filters nodes based on a predicate.

@param n - A pointer to the node.
@param p - A predicate function to determine whether to keep a node.
@return - A pointer to the head of the filtered nodes list.

This function recursively filters the linked list of nodes, keeping only those
nodes for which the predicate function returns true. It frees the memory of the nodes
that do not satisfy the predicate.
*/
/*@
struct node *nodes_filter(struct node *n, int_predicate *p)
    //@ requires nodes(n, ?l) &*& [_]int_predicate_type(p)(?fp);
    //@ ensures nodes(result, filter_fp(fp, l)) &*& [_]int_predicate_type(p)(fp);
@*/
struct node *nodes_filter(struct node *n, int_predicate *p)
{
    //@ open nodes(n, l);
    if (n == 0)
    {
        //@ close nodes(0, nil);
        return 0;
    }
    else
    {
        //@ n->value |-> ?v;
        //@ n->next |-> ?next;
        bool keep = p(n->value);
        //@ assert [_]int_predicate_type(p)(?fp);
        struct node *next_filtered = nodes_filter(n->next, p);
        if (keep)
        {
            n->next = next_filtered;
            //@ close nodes(n, cons(v, filter_fp(fp, ?rest)));
            return n;
        }
        else
        {
            //@ nodes_dispose(n);
            free(n);
            return next_filtered;
        }
    }
}

/***
 * Description:
The stack_filter function filters the stack based on a predicate.

@param stack - A pointer to the stack.
@param p - A predicate function to determine whether to keep a node.

This function filters the nodes in the stack using the given predicate function.
It updates the stack to contain only the nodes that satisfy the predicate.
*/
/*@
void stack_filter(struct stack *stack, int_predicate *p)
    //@ requires stack(stack, ?l) &*& [_]int_predicate_type(p)(?fp);
    //@ ensures stack(stack, filter_fp(fp, l)) &*& [_]int_predicate_type(p)(fp);
@*/
void stack_filter(struct stack *stack, int_predicate *p)
{
    //@ open stack(stack, l);
    struct node *filtered_head = nodes_filter(stack->head, p);
    stack->head = filtered_head;
    //@ close stack(stack, filter_fp(fp, l));
}

/***
 * Description:
The nodes_dispose function disposes of all nodes in a linked list.

@param n - A pointer to the head node.

This function recursively frees all nodes in the linked list.
*/
/*@
void nodes_dispose(struct node *n)
    //@ requires nodes(n, _);
    //@ ensures true;
@*/
void nodes_dispose(struct node *n)
{
    //@ open nodes(n, _);
    if (n != 0)
    {
        nodes_dispose(n->next);
        //@ open nodes(n, _);
        //@ n->value |-> _;
        //@ n->next |-> _;
        free(n);
    }
}

/***
 * Description:
The stack_dispose function disposes of a stack.

@param stack - A pointer to the stack.

This function frees all nodes in the stack and then frees the stack itself.
*/
/*@
void stack_dispose(struct stack *stack)
    //@ requires stack(stack, _);
    //@ ensures true;
@*/
void stack_dispose(struct stack *stack)
{
    //@ open stack(stack, _);
    nodes_dispose(stack->head);
    free(stack);
}

/***
 * Description:
The neq_20 function checks if x is not equal to 20.

@param x - The integer to check.
@return - true if x is not equal to 20, false otherwise.
*/
/*@
bool neq_20(int x)
    //@ requires [_]int_predicate_type(neq_20)(?fp);
    //@ ensures [_]int_predicate_type(neq_20)(fp) &*& result == fp(x);
@*/
bool neq_20(int x)
{
    //@ neq_20_is_int_predicate();
    return x != 20;
}

/***
 * Description:
The main function creates a stack, pushes some integers into it,
filters out some integers from the stack and finally disposes the stack.
*/
/*@
int main()
    //@ requires true;
    //@ ensures true;
@*/
int main()
{
    //@ neq_20_is_int_predicate();
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    stack_push(s, 30);
    stack_filter(s, neq_20);
    stack_dispose(s);
    return 0;
}
```
