#include "stdlib.h"
//@ #include "maps.gh"

struct node {
  void* val;
  struct node* next;
};

struct set {
  struct node* head;
};


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
{
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
}

