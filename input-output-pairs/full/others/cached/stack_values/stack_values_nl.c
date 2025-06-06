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

/***
 * Description:
The create_stack function creates a stack.

@param none

This function makes sure to return a new empty stack.
*/
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
The stack_push function pushes a new integer value onto the stack.

@param stack - A pointer to a stack
@param value - The integer value to be added on top on the stack

The function ensures that the new value is added to the top of stack.
*/
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
The stack_pop function pops the head of a non-empty stack out and returns its value.

@param stack - A pointer to a non-empty stack

The function ensures that changed stack is the tail of the original stack, 
and the return value is the head of the original stack.
*/
int stack_pop(struct stack *stack)
{
    struct node *head = stack->head;
    int result = head->value;
    stack->head = head->next;
    free(head);
    return result;
}

/***
 * Description:
The stack_reverse function iteratively reverse the elements of a stack. 

@param stack - pointer to the stack to be reversed.

The function ensures that the stack is reversed in place,
*/
void stack_reverse(struct stack *stack)
{
    struct node *n = stack->head;
    struct node *m = 0;
    while (n != 0)
    {
        struct node *next = n->next;
        n->next = m;
        m = n;
        n = next;
    }
    stack->head = m;
}

/***
 * Description:
The stack_dispose function frees a stack.

@param stack- A pointer to a stack

The function makes sure that the stack is freed. 
*/
void stack_dispose(struct stack *s)
{
  struct node* n = s->head;
  while(n != 0) 
  {
    struct node* tmp = n;
    n = n->next;
    free(tmp);
  }
  free(s);
}

/***
 * Description:
The main function that checks the functionality of stack operations.
*/
int main()
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    int result1 = stack_pop(s);
    assert(result1 == 20);
    int result2 = stack_pop(s);
    assert(result2 == 10);
    stack_dispose(s);
    return 0;
}