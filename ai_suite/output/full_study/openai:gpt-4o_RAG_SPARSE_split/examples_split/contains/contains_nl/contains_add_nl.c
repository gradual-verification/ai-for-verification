#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};

/*@

predicate nodes(struct node* n; list<void*> vs) =
  n == 0 ? 
    vs == nil 
  : 
    n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next, ?vs0) &*& vs == cons(v, vs0);

@*/

// TODO: make this function pass the verification
/*add() function
-params: struct node* n, void* v
-description: add a new element to the list. 
It requires that n is the starting node of the list. 
It ensures that the element is added to the head of the list.
*/
/*@

requires nodes(n, ?vs);
ensures nodes(result, cons(v, vs));

@*/
struct node* add(struct node* n, void* v) 
{
  struct node* nn = malloc(sizeof(struct node));
  if(nn == 0) abort();
  nn->value = v;
  nn->next = n;
  //@ close nodes(nn, cons(v, vs));
  return nn;
}