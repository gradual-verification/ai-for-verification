#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};

//@ predicate nodes(struct node* n; list<void*> values) =
//@   n == 0 ?
//@     values == nil
//@   :
//@     n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next, ?values0) &*& values == cons(v, values0);

// TODO: make this function pass the verification
/*create_list() function
-params: none
-description: return an empty list. */
struct node* create_list() 
  //@ requires true;
  //@ ensures nodes(result, nil);
{
  return 0;
  //@ close nodes(0, nil);
}