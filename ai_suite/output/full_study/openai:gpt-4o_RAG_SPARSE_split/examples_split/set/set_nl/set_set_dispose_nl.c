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
predicate nodes(struct node* n) =
  n == 0 ? true : n->val |-> _ &*& n->next |-> ?next &*& malloc_block(n, sizeof(struct node)) &*& nodes(next);

predicate set(struct set* s) =
  s->head |-> ?head &*& malloc_block(s, sizeof(struct set)) &*& nodes(head);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The set_dispose function disposes of the set by freeing all allocated memory.

@param set - A pointer to the set to be disposed of.
@requires - The set must be valid.
@ensures - All memory associated with the set is freed. 
*/
void set_dispose(struct set* set)
  //@ requires set(set);
  //@ ensures true;
{
  struct node* curr = set->head;
  while(curr != 0) 
    //@ invariant nodes(curr);
  {
    struct node* nxt = curr->next;
    //@ open nodes(curr);
    free(curr);
    curr = nxt;
  }
  //@ open nodes(0);
  free(set);
}