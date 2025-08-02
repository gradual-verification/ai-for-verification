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
predicate nodes(struct node* n, list<void*> vs) =
  n == 0 ? 
    vs == nil 
  : 
    n->val |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next, ?vs0) &*& vs == cons(v, vs0);

predicate set(struct set* s, list<void*> vs) =
  s->head |-> ?head &*& malloc_block_set(s) &*& nodes(head, vs);

fixpoint bool not_in_set(void* x, list<void*> vs) {
  return !mem(x, vs);
}
@*/

// TODO: make this function pass the verification
/*** 
 * Description:
The set_add function adds a new element to the set.

@param set - A pointer to the set.
@param x - A pointer to the element to be added.
@requires - The set must be valid and x must not already be in the set.
@ensures - The set is updated to include x, and the size of the set is incremented by one.
*/
void set_add(struct set* set, void* x)
  //@ requires set(set, ?vs) &*& not_in_set(x, vs);
  //@ ensures set(set, cons(x, vs));
{
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
  //@ close nodes(n, cons(x, vs));
  //@ close set(set, cons(x, vs));
}