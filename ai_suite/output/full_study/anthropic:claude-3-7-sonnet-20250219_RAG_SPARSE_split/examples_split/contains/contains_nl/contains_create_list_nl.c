#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};

/*@
// Define a predicate for a linked list of nodes
predicate nodes(struct node* n; list<void*> values) =
    n == 0 ?
        values == nil
    :
        n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*&
        nodes(next, ?tail) &*& values == cons(v, tail);
@*/

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