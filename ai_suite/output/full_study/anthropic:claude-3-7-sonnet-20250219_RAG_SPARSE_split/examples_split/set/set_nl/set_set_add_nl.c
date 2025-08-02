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
// Define a predicate for a linked list of nodes representing a set
predicate nodes(struct node* n; list<void*> values) =
  n == 0 ?
    values == nil
  :
    n->val |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*&
    nodes(next, ?rest) &*& values == cons(v, rest);

// Define a predicate for the set structure
predicate set(struct set* s; list<void*> values) =
  s->head |-> ?head &*& nodes(head, values) &*& malloc_block_set(s);

// Helper lemma to check if an element is in a list
lemma bool mem_check(void* x, list<void*> values)
  requires true;
  ensures result == mem(x, values);
{
  switch(values) {
    case nil: return false;
    case cons(h, t): 
      if(h == x) return true;
      else return mem_check(x, t);
  }
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
/*@
requires set(set, ?values) &*& !mem(x, values);
ensures set(set, cons(x, values));
@*/
void set_add(struct set* set, void* x)
{
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  //@ open set(set, values);
  n->next = set->head;
  n->val = x;
  set->head = n;
  //@ close nodes(n, cons(x, values));
  //@ close set(set, cons(x, values));
}