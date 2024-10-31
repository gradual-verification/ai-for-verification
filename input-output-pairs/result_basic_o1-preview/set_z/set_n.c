#include "stdlib.h"
//@ #include "lists.gh"

struct node {
  void* val;
  struct node* next;
};

struct set {
  struct node* head;
};

//@ predicate nodes(struct node* n, list<void*> vs) =
//@   n == 0 ? vs == nil : n->val |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next, ?vs_tail) &*& vs == cons(v, vs_tail);

//@ predicate set(struct set* set, list<void*> vs) =
//@   set != 0 &*& set->head |-> ?h &*& nodes(h, vs) &*& malloc_block_set(set);

/***
 * Description:
The create_set function creates a new, empty set.

@param - None.
@requires - No specific preconditions.
@ensures - Returns a pointer to a newly allocated set if successful, or 0 if memory allocation fails. The set is initially empty.
*/
//@ requires emp;
//@ ensures result == 0 ? emp : set(result, nil);
struct set* create_set()
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
@requires - The set must be valid and x must not already be in the set, and x != 0.
@ensures - The set is updated to include x.
*/
//@ requires set(set, ?vs) &*& x != 0 &*& mem(x, vs) == false;
//@ ensures set(set, cons(x, vs));
void set_add(struct set* set, void* x)
{
  //@ open set(set, vs);
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
@requires - The set must be valid.
@ensures - Returns true if x is present in the set, otherwise returns false. The set remains unchanged.
*/
//@ requires set(set, ?vs);
//@ ensures set(set, vs) &*& result == mem(x, vs);
bool set_contains(struct set* set, void* x)
{
  //@ open set(set, vs);
  struct node* curr = set->head;
  bool found = false;
  //@ list<void*> vs_rest = vs;
  while(curr != 0 && !found)
  /*@
    invariant nodes(curr, vs_rest) &*&
              found == mem(x, vs \ vs_rest);
  @*/
  {
    //@ open nodes(curr, vs_rest);
    if(curr->val == x) {
      found = true;
    }
    curr = curr->next;
    //@ vs_rest = tail(vs_rest);
    //@ close nodes(curr, vs_rest);
  }
  //@ close nodes(curr, vs_rest);
  //@ close set(set, vs);
  return found;
}

/***
 * Description:
The set_dispose function disposes of the set by freeing all allocated memory.

@param set - A pointer to the set to be disposed of.
@requires - The set must be valid.
@ensures - All memory associated with the set is freed, and the set is no longer valid.
*/
//@ requires set(set, ?vs);
//@ ensures emp;
void set_dispose(struct set* set)
{
  //@ open set(set, vs);
  struct node* curr = set->head;
  while(curr != 0)
  //@ invariant nodes(curr, _);
  {
    //@ open nodes(curr, _);
    struct node* nxt = curr->next;
    free(curr);
    curr = nxt;
  }
  //@ open nodes(curr, _); // curr == 0
  free(set);
}

/***
* Description:
The main function demonstrates the use of the set data structure.

@param - None.
@requires - No specific preconditions.
@ensures - Adds elements to the set, checks for their existence, and then disposes of the set.
*/
//@ requires emp;
//@ ensures emp;
int main()
{
  struct set* set = create_set();
  if(set == 0) return 0;
  //@ list<void*> vs = nil;
  set_add(set, (void*)1);
  //@ vs = cons((void*)1, vs);
  set_add(set, (void*)2);
  //@ vs = cons((void*)2, vs);
  set_add(set, (void*)3);
  //@ vs = cons((void*)3, vs);
  bool cnt = set_contains(set, (void*)1);
  //@ assert mem((void*)1, vs) == true;
  assert(cnt);
  set_dispose(set);
  return 0;
}
