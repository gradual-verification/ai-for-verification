#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};

// specific to cell

struct cell {
  int val;
};

/*@
// Define a predicate for a node in the linked list
predicate node(struct node* n; void* v, struct node* next) =
  n->value |-> v &*& n->next |-> next &*& malloc_block_node(n);

// Define a predicate for a linked list
predicate nodes(struct node* n; list<void*> values) =
  n == 0 ?
    values == nil
  :
    node(n, ?v, ?next) &*& nodes(next, ?tail) &*& values == cons(v, tail);

// Define a predicate for a cell
predicate cell(struct cell* c; int v) =
  c->val |-> v &*& malloc_block_cell(c);
@*/

// TODO: make this function pass the verification
/*add() function
-params: struct node* n, void* v
-description: add a new element to the list. 
It requires that n is the starting node of the list. 
It ensures that the element is added to the head of the list.
*/
struct node* add(struct node* n, void* v) 
//@ requires nodes(n, ?values);
//@ ensures nodes(result, cons(v, values));
{
  struct node* nn = malloc(sizeof(struct node));
  if(nn == 0) abort();
  nn->value = v;
  nn->next = n;
  //@ close node(nn, v, n);
  //@ close nodes(nn, cons(v, values));
  return nn;
}