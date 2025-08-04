#include "stdlib.h"
//@ #include "list.gh"

struct node {
  void* value;
  struct node* next;
};

// specific to cell

struct cell {
  int val;
};

/*@
predicate nodes(struct node *n; list<void*> values) =
    n == 0 ?
        values == nil
    :
        n->value |-> ?v &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        nodes(next, ?rest) &*&
        values == cons(v, rest);
@*/


// TODO: make this function pass the verification
/*add() function
-params: struct node* n, void* v
-description: add a new element to the list. 
It requires that n is the starting node of the list. 
It ensures that the element is added to the head of the list.
*/
struct node* add(struct node* n, void* v)
    //@ requires nodes(n, ?vs) &*& pointer_within_limits(v) == true;
    //@ ensures nodes(result, cons(v, vs));
{
  struct node* nn = malloc(sizeof(struct node));
  if(nn == 0) abort();
  nn->value = v;
  nn->next = n;
  return nn;
}