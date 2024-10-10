#include "stdlib.h"

// Predicates for VeriFast
/*@
predicate node(struct node *n; struct node *next, int value) =
    n->next |-> next &*& n->value |-> value;

predicate stack(struct stack *s; struct node *head) =
    s->head |-> head;

predicate nodes(struct node *head) =
    head == 0 ? true : node(head, ?next, ?value) &*& nodes(next);
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

/***
 * Description:
 * The create_stack function creates a stack.
 *
 * @param none
 *
 * This function creates a new stack by allocating memory for
 * the struct stack. The parameter is void as it doesn't take
 * any input. It initializes the head of the stack to NULL.
 */
/*@
requires true;
ensures stack(result, 0);
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

/***
 * Description:
 * The stack_push function pushes a new integer value onto the stack.
 *
 * @param stack - A pointer to a stack
 * @param value - The integer value to be added on top on the stack
 *
 * It takes a struct stack pointer and an integer value as parameters.
 * It creates a new node to hold the value and links it to the current
 * head of the stack. Then, it updates the head of the stack to
 * point to the newly added node. The function ensures that the new value
 * is successfully added to the stack.
 */
/*@
requires stack(stack, ?head) &*& nodes(head);
ensures stack(stack, ?newHead) &*& nodes(newHead);
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

/***
 * Description:
 * The stack_dispose function deletes an empty stack.
 *
 * @param stack - A pointer to a stack whose values are empty
 *
 * The function disposes of the stack by freeing the memory
 * allocated for the struct stack. It takes a struct stack
 * pointer as a parameter. The purpose of this function is to
 * deallocate the memory used by the stack once it is no longer
 * needed.
 */
/*@
requires stack(stack, 0);
ensures emp;
@*/
void stack_dispose(struct stack *stack)
{
    free(stack);
}

int main()
{
    return 0;
}
