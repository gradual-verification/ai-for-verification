#include "stdlib.h"
#include "stdbool.h"
//@ #include "maps.gh"

struct node {
  void* val;
  struct node* next;
};

struct set {
  struct node* head;
};

/*** 
 * Description:
The create_set function creates a new, empty set.

@param - None.
@requires - No specific preconditions.
@ensures - Returns a pointer to a newly allocated set if successful, or 0 if memory allocation fails. The set is initially empty.
*/
struct set* create_set()
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
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
{
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
}

/***
 * Description: 
The set_contains function checks whether a given element is present in the set.

@param set - A pointer to the set.
@param x - A pointer to the element to check for.
@requires - The set must be valid.
@ensures - Returns true if x is present in the set, otherwise returns false. The set remains unchanged.
*/
bool set_contains(struct set* set, void* x)
{
  struct node* curr = set->head;
  bool found = false;
  while(curr != 0 && ! found) 
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
The set_dispose function disposes of the set by freeing all allocated memory.

@param set - A pointer to the set to be disposed of.
@requires - The set must be valid.
@ensures - All memory associated with the set is freed, and the set is no longer valid.
*/
void set_dispose(struct set* set)
{
  struct node* curr = set->head;
  while(curr != 0) 
  {
    struct node* nxt = curr->next;
    free(curr);
    curr = nxt;
  }
  free(set);
}

/***
* Description:
The main function demonstrates the use of the set data structure.

@param - None.
@requires - No specific preconditions.
@ensures - Adds elements to the set, checks for their existence, and then disposes of the set.
*/
int main() 
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
