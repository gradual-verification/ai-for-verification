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

/***
 * Description: 
The set_contains function checks whether a given element is present in the set.

@param set - A pointer to the set.
@param x - A pointer to the element to check for.
@ensures - Returns true if x is present in the set, otherwise returns false. The set remains unchanged.
*/
bool set_contains(struct set* set, void* x)
  //@ requires set(set, ?values);
  //@ ensures set(set, values) &*& result == mem(x, values);
{
  //@ open set(set, values);
  struct node* curr = set->head;
  //@ open nodes(curr, values);
  bool found = false;
  
  //@ list<void*> visited = nil;
  while(curr != 0 && !found) 
    /*@ invariant curr == 0 ? 
          nodes(curr, nil) &*& visited == values
        : 
          curr->val |-> ?cv &*& curr->next |-> ?cnext &*& malloc_block_node(curr) &*& 
          nodes(cnext, ?remaining) &*& values == append(visited, cons(cv, remaining)) &*&
          found == mem(x, visited); @*/
  {
    if(curr->val == x) {
      found = true;
      //@ visited = append(visited, cons(curr->val, nil));
    } else {
      //@ visited = append(visited, cons(curr->val, nil));
      //@ void* old_val = curr->val;
      struct node* old_next = curr->next;
      curr = curr->next;
      //@ open nodes(old_next, remaining);
    }
  }
  
  //@ if (curr == 0) close nodes(curr, nil);
  //@ close nodes(set->head, values);
  //@ close set(set, values);
  return found;
}