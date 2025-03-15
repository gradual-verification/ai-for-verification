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
 * The function allocates memory for a `stack` and sets its head to `NULL`. It returns the pointer to that stack. 
 * If memory allocation fails, the program terminates.
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
 * The function allocates memory for a new `node`, sets its value, 
 * updates the `next` pointer to point to the previous head, and 
 * assigns it as the new head of the stack.
 * If memory allocation fails, the program terminates.
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
 * @param s - A pointer to the stack.
 *
 * The function retrieves the value of the top node, updates the 
 * stack head pointer, frees the removed node, and returns its value.
 * If the stack is empty, the function should not be called.
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
 * The function iterates through all nodes in the stack, freeing them one by one.
 * Finally, it frees the stack structure itself.
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
 * The function iterates through the stack, counting the number of nodes.
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
 *
 * It creates a stack, pushes three values onto it, pops three values,
 * asserts the expected values, and then disposes of the stack.
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
