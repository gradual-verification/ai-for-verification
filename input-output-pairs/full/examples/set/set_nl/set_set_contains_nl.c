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
The set_contains function checks whether a given element is present in the set.

@param set - A pointer to the set.
@param x - A pointer to the element to check for.
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

