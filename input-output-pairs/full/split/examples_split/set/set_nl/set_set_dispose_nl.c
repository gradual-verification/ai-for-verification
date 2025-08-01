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
The set_dispose function disposes of the set by freeing all allocated memory.

@param set - A pointer to the set to be disposed of.
@requires - The set must be valid.
@ensures - All memory associated with the set is freed. 
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

