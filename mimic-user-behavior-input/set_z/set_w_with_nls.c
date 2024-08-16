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
predicate lseg(struct node* first, struct node* last, list<void*> vs) =
  first == last ?
    vs == nil
  :
    first->val |-> ?val &*& first->next |-> ?next &*& malloc_block_node(first) &*& lseg(next, last, ?tail);

predicate set(struct set* set) =
  set->head |-> ?head &*& malloc_block_set(set) &*& lseg(head, 0, _);
@*/

/*
  Weaker Specification:
  - Description: Creates a new, empty set.
  - Weaker Preconditions: No specific preconditions.
  - Weaker Postconditions: Returns a pointer to a newly allocated set if successful, or `0` if memory allocation fails.
*/
struct set* create_set()
  //@ requires true;
  //@ ensures result == 0 ? true : set(result);
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
  //@ close lseg(0, 0, nil);
  //@ close set(set);
  return set;
}

/*
  Weaker Specification:
  - Description: Adds a new element to the set.
  - Weaker Preconditions: The set must be valid.
  - Weaker Postconditions: The set is updated to include the new element.
*/
void set_add(struct set* set, void* x)
  //@ requires set(set);
  //@ ensures set(set);
{
  //@ open set(set);
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
  //@ close lseg(n, 0, _);
  //@ close set(set);
}

/*
  Weaker Specification:
  - Description: Checks whether a given element is present in the set.
  - Weaker Preconditions: The set must be valid.
  - Weaker Postconditions: Returns `true` if the element is found, otherwise `false`. The set remains unchanged.
*/
bool set_contains(struct set* set, void* x)
  //@ requires set(set);
  //@ ensures set(set) &*& result ? true : true;
{
  //@ open set(set);
  struct node* curr = set->head;
  bool found = false;
  while(curr != 0 && !found) 
    //@ requires lseg(curr, 0, _);
    //@ ensures lseg(curr, 0, _);
  {
    //@ open lseg(curr, 0, _);
    if(curr->val == x) {
      found = true;
    }
    curr = curr->next;
    //@ close lseg(curr, 0, _);
  }
  //@ close set(set);
  return found;
}

/*
  Weaker Specification:
  - Description: Disposes of the set by freeing all allocated memory.
  - Weaker Preconditions: The set must be valid.
  - Weaker Postconditions: All memory associated with the set is freed.
*/
void set_dispose(struct set* set)
  //@ requires set(set);
  //@ ensures true;
{
  //@ open set(set);
  struct node* curr = set->head;
  while(curr != 0) 
    //@ invariant lseg(curr, 0, _);
  {
    //@ open lseg(curr, 0, _);
    struct node* nxt = curr->next;
    free(curr);
    curr = nxt;
  }
  //@ open lseg(curr, 0, _);
  free(set);
}

/*
  Weaker Specification:
  - Description: Main function demonstrating the use of the set data structure.
  - Weaker Preconditions: No specific preconditions.
  - Weaker Postconditions: The set is created, elements are added, and it is disposed of correctly.
*/
int main() //@ : main
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
