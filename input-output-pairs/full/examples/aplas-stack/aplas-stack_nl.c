#include "stdlib.h"

/***
 * Description:
 * The `node` structure represents an element in the stack.
 * Each node stores an integer value and a pointer to the next node.
 */
struct node {
  struct node* next;
  int value;
};

/***
 * Description:
 * The `stack` structure represents a linked list-based stack.
 * It contains a pointer to the head node of the stack.
 */
struct stack {
  struct node* head;
};

/***
 * Description:
 * The `create_stack` function initializes an empty stack.
 *
 * @param none
 * 
 * The function makes sure that the return value is a stack whose elements are empty.
 */
struct stack* create_stack() 
{
  struct stack* s = malloc(sizeof(struct stack));
  if(s == 0) abort();
  s->head = 0;
  return s;
}

/***
 * Description:
 * The `push` function adds a new integer value to the top of the stack.
 *
 * @param s - A pointer to the stack.
 * @param x - The integer value to be pushed onto the stack.
 *
 * The function makes sure that value x is at the top of the new stack.
 */
void push(struct stack* s, int x)
{
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = s->head;
  n->value = x;
  s->head = n;
}

/***
 * Description:
 * The `pop` function removes and returns the top value of the stack.
 *
 * @param s - A pointer to the stack, which is not empty.
 *
 * The function makes sure that the new stack is the tail of the original stack,
 * and that the return value is the top value of the original stack.
 */
int pop(struct stack* s)
{
  struct node* tmp = s->head;
  int res = tmp->value;
  s->head = tmp->next;
  free(tmp);
  return res;
}

/***
 * Description:
 * The `dispose` function frees all memory allocated for the stack.
 *
 * @param s - A pointer to the stack.
 *
 * The function makes sure that all the nodes in the stack are freed.
 */
void dispose(struct stack* s) 
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
 * The `get_length` function calculates and returns the number of elements in the stack.
 *
 * @param s - A pointer to the stack.
 *
 * The function makes sure to return the number of nodes.
 */
int get_length(struct stack* s) 
{
  int r = 0;
  struct node* n = s->head;
  while(n != 0) 
  {
    r = r + 1;
    n = n->next;
  }
  return r;
}

/***
 * Description:
 * The `main` function demonstrates the use of the stack data structure.
 */
int main()
{
  struct stack* s = create_stack();
  push(s, 1);
  push(s, 2);
  push(s, 3);
  int r1 = pop(s);
  int r2 = pop(s);
  int r3 = pop(s);
  assert(r3 == 1);
  dispose(s);
  return 0;
}
