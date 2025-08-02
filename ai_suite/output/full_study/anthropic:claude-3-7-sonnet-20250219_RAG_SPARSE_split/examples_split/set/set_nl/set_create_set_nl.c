#include "stdlib.h"
//@ #include "maps.gh"

struct node {
  void* val;
  struct node* next;
};

struct set {
  struct node* head;
};

/*@
// Define a predicate for a linked list of nodes
predicate nodes(struct node* n; list<void*> values) =
  n == 0 ?
    values == nil
  :
    n->val |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*&
    nodes(next, ?rest) &*& values == cons(v, rest);

// Define a predicate for the set structure
predicate set(struct set* s; list<void*> values) =
  s->head |-> ?head &*& nodes(head, values) &*& malloc_block_set(s);
@*/

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
  //@ if (set == 0) return 0;
  if(set == 0) return 0;
  set->head = 0;
  //@ close nodes(0, nil);
  //@ close set(set, nil);
  return set;
}