#include "stdlib.h"

/*@
// Define a predicate for a linked list node
predicate node_pred(struct node* n; void* value, struct node* next) =
    n->value |-> value &*& n->next |-> next &*& malloc_block_node(n);

// Define a predicate for a linked list
predicate nodes(struct node* n; list<void*> values) =
    n == 0 ?
        values == nil
    :
        node_pred(n, ?v, ?next) &*& nodes(next, ?rest) &*& values == cons(v, rest);
@*/

struct node {
  void* value;
  struct node* next;
};

// TODO: make this function pass the verification
/*add() function
-params: struct node* n, void* v
-description: add a new element to the list. 
It requires that n is the starting node of the list. 
It ensures that the element is added to the head of the list.
*/
/*@
// Specification for add function
requires nodes(n, ?values);
ensures nodes(result, cons(v, values));
@*/
struct node* add(struct node* n, void* v) 
{
  struct node* nn = malloc(sizeof(struct node));
  if(nn == 0) abort();
  nn->value = v;
  nn->next = n;
  //@ close node_pred(nn, v, n);
  //@ close nodes(nn, cons(v, values));
  return nn;
}