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
predicate nodes(struct node* n, list<void*> values) =
  n == 0 ?
    values == nil
  :
    n->val |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*&
    nodes(next, ?rest) &*& values == cons(v, rest);

// Define a predicate for the set
predicate set(struct set* s, list<void*> values) =
  s->head |-> ?head &*& nodes(head, values) &*& malloc_block_set(s);
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
//@ requires set(set, ?values);
//@ ensures set(set, cons(x, values));
{
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  //@ open set(set, values);
  set->head = n;
  //@ close nodes(n, cons(x, values));
  //@ close set(set, cons(x, values));
}


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
  bool found = false;
  //@ list<void*> remaining = values;
  
  while(curr != 0 && !found) 
  /*@ invariant nodes(curr, remaining) &*& found ? mem(x, values) : 
                 (mem(x, remaining) ? mem(x, values) : !mem(x, values)); @*/
  {
    //@ open nodes(curr, remaining);
    if(curr->val == x) {
      found = true;
    }
    curr = curr->next;
    //@ remaining = tail(remaining);
  }
  //@ close set(set, values);
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
//@ requires set(set, ?values);
//@ ensures true;
{
  //@ open set(set, values);
  struct node* curr = set->head;
  //@ open nodes(curr, values);
  while(curr != 0) 
  //@ invariant curr == 0 ? true : nodes(curr, ?remaining);
  {
    //@ if (curr != 0) open nodes(curr, remaining);
    struct node* nxt = curr->next;
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