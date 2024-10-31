#include "stdlib.h"
//@ #include "maps.gh"

//@ predicate nodes(struct node* n, predicate(void*) p) = n == 0 ? true : malloc_block_node(n) &*& p(n->val) &*& nodes(n->next, p);

struct node {
  void* val;
  struct node* next;
};

//@ predicate set(struct set* s, predicate(void*) p) = malloc_block_set(s) &*& nodes(s->head, p);

struct set {
  struct node* head;
};

/*** 
 * Description:
 * The create_set function creates a new, empty set.
 *
 * @param - None.
 * @requires - No specific preconditions.
 * @ensures - Returns a pointer to a newly allocated set if successful,
 *            or 0 if memory allocation fails. The set is initially empty.
*/
//@ ensures result == 0 ? true : set(result, p);
struct set* create_set()
  //@ requires true;
  //@ ensures result == 0 ? true : set(result, p);
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
  //@ close nodes(0, p);
  //@ close set(set, p);
  return set;
}

/*** 
 * Description:
 * The set_add function adds a new element to the set.
 *
 * @param set - A pointer to the set.
 * @param x - A pointer to the element to be added.
 * @requires - The set must be valid and x must not already be in the set.
 * @ensures - The set is updated to include x, and the size of the set is incremented by one.
*/
//@ requires set(set, p) &*& p(x);
//@ ensures set(set, p);
void set_add(struct set* set, void* x)
  //@ requires set(set, p) &*& p(x);
  //@ ensures set(set, p);
{
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
  //@ close nodes(n, p);
  //@ close set(set, p);
}

/***
 * Description: 
 * The set_contains function checks whether a given element is present in the set.
 *
 * @param set - A pointer to the set.
 * @param x - A pointer to the element to check for.
 * @requires - The set must be valid.
 * @ensures - Returns true if x is present in the set, otherwise returns false.
 *            The set remains unchanged.
*/
//@ requires set(set, p);
//@ ensures set(set, p) &*& (result == true ? p(x) : true);
bool set_contains(struct set* set, void* x)
  //@ requires set(set, p);
  //@ ensures set(set, p) &*& (result == true ? p(x) : true);
{
  struct node* curr = set->head;
  bool found = false;
  while(curr != 0 && !found) 
    //@ invariant nodes(curr, p) &*& found == false ? true : p(x);
  {
    if(curr->val == x) {
      found = true;
    }
    curr = curr->next;
  }
  return found;
}

/***
 * Description:
 * The set_dispose function disposes of the set by freeing all allocated memory.
 *
 * @param set - A pointer to the set to be disposed of.
 * @requires - The set must be valid.
 * @ensures - All memory associated with the set is freed, and the set is no longer valid.
*/
//@ requires set(set, p);
//@ ensures true;
void set_dispose(struct set* set)
  //@ requires set(set, p);
  //@ ensures true;
{
  struct node* curr = set->head;
  while(curr != 0) 
    //@ invariant nodes(curr, p);
  {
    struct node* nxt = curr->next;
    free(curr);
    curr = nxt;
  }
  free(set);
}

/***
* Description:
* The main function demonstrates the use of the set data structure.
*
* @param - None.
* @requires - No specific preconditions.
* @ensures - Adds elements to the set, checks for their existence, and then disposes of the set.
*/
//@ requires true;
//@ ensures true;
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
