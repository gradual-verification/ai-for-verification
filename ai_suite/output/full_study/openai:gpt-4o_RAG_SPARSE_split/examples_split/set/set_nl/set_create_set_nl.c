#include "stdlib.h"
//@ #include "maps.gh"

struct node {
  void* val;
  struct node* next;
};

struct set {
  struct node* head;
};

//@ predicate nodes(struct node* n; list<void*> vs) = 
//@   n == 0 ? vs == nil : n->val |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next, ?vs0) &*& vs == cons(v, vs0);

//@ predicate set(struct set* s; list<void*> vs) = 
//@   s->head |-> ?head &*& nodes(head, vs) &*& malloc_block_set(s);

// TODO: make this function pass the verification
/*** 
 * Description:
The create_set function creates a new, empty set.

@param - None.
@requires - No specific preconditions.
@ensures - Returns a pointer to a newly allocated set if successful, or 0. The set is initially empty.
*/
struct set* create_set()
  //@ requires true;
  //@ ensures result == 0 ? true : set(result, nil);
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
  //@ close nodes(0, nil);
  //@ close set(set, nil);
  return set;
}