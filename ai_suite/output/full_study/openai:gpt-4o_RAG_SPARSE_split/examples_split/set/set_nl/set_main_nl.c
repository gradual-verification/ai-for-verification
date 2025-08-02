#include "stdlib.h"
#include <stdbool.h>
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

/*** 
 * Description:
The set_add function adds a new element to the set.

@param set - A pointer to the set.
@param x - A pointer to the element to be added.
@requires - The set must be valid and x must not already be in the set.
@ensures - The set is updated to include x, and the size of the set is incremented by one.
*/
void set_add(struct set* set, void* x)
  //@ requires set(set, ?vs) &*& !mem(x, vs);
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
  while(curr != 0 && ! found) 
    //@ invariant nodes(curr, ?vs0) &*& append(vs0, ?vs1) == vs &*& found == mem(x, vs0);
  {
    if(curr->val == x) {
      found = true;
    }
    curr = curr->next;
  }
  //@ close set(set, vs);
  return found;
}

/***
 * Description:
The set_dispose function disposes of the set by freeing all allocated memory.

@param set - A pointer to the set to be disposed of.
@requires - The set must be valid.
@ensures - All memory associated with the set is freed. 
*/
void set_dispose(struct set* set)
  //@ requires set(set, _);
  //@ ensures true;
{
  struct node* curr = set->head;
  while(curr != 0) 
    //@ invariant nodes(curr, _);
  {
    struct node* nxt = curr->next;
    //@ open nodes(curr, _);
    free(curr);
    curr = nxt;
  }
  free(set);
}

// TODO: make this function pass the verification
/***
* Description:
The main function demonstrates the use of the set data structure.
*/
int main() 
  //@ requires true;
  //@ ensures true;
{
  struct set* set = create_set();
  if(set == 0) return 0;
  set_add(set, (void*) 1);
  set_add(set, (void*) 2);
  set_add(set, (void*) 3);
  bool cnt = set_contains(set, (void*) 1);
  assert(cnt);
  set_dispose(set);
  return 0;
}