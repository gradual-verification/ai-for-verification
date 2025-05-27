#include "stdlib.h"

struct node {
  struct node* next;
  int value;
};

struct stack {
  struct node* head;
};

/***
 * Description:
 * The create_stack function dynamically allocates and initializes an empty stack.
 * 
 * @param None
 * 
 * The function allocates memory for a stack structure and sets its head pointer to null, indicating the stack is empty.
 * If memory allocation fails, the program aborts.
 * It guarantees that the returned stack is properly initialized and contains no elements.
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
 * The push function adds a new element to the top of the stack.
 * 
 * @param s - a pointer to a valid, initialized stack.
 * @param x - an integer value to be pushed onto the stack.
 * 
 * The function allocates memory for a new node, stores the value `x` in the node,
 * and updates the stack's head pointer to point to this new node.
 * If memory allocation fails, the program aborts.
 * After the call, the stack contains all previously pushed values with `x` added to the top.
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
 * The clear function deallocates all memory used by the stack and its elements.
 * 
 * @param s - a pointer to a stack whose elements are to be cleared.
 * 
 * The function iterates through the linked list of nodes starting from the stack's head,
 * freeing each node in sequence. Finally, it frees the memory allocated to the stack structure itself.
 * After calling this function, the memory used by the stack and all of its elements is released.
 */
void clear(struct stack* s) 
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
 * The main function demonstrates basic usage of the stack.
 * 
 * It creates an empty stack, pushes a single element (1) onto it, and then clears the stack to free memory.
 * The program terminates successfully.
 */
int main()
{
  struct stack* s = create_stack();
  push(s, 1);
  clear(s);
  return 0;
}
