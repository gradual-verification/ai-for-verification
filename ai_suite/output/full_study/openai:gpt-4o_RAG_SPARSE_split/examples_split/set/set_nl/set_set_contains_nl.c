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
predicate nodes(struct node* n; list<void*> vs) =
  n == 0 ? vs == nil : n->val |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next, ?vs0) &*& vs == cons(v, vs0);

predicate set(struct set* s; list<void*> vs) =
  s->head |-> ?head &*& malloc_block_set(s) &*& nodes(head, vs);
@*/

// TODO: make this function pass the verification
/***
 * Description: 
The set_contains function checks whether a given element is present in the set.

@param set - A pointer to the set.
@param x - A pointer to the element to check for.
@ensures - Returns true if x is present in the set, otherwise returns false. The set remains unchanged.
*/
bool set_contains(struct set* set, void* x)
  //@ requires set(set, ?vs);
  //@ ensures set(set, vs) &*& result == mem(x, vs);
{
  struct node* curr = set->head;
  bool found = false;
  //@ open set(set, vs);
  //@ open nodes(curr, vs);
  while(curr != 0 && !found) 
    //@ invariant nodes(curr, ?vs0) &*& mem(x, vs) == (found || mem(x, vs0));
  {
    if(curr->val == x) {
      found = true;
    }
    curr = curr->next;
    //@ open nodes(curr, _);
  }
  //@ close nodes(curr, _);
  //@ close set(set, vs);
  return found;
}