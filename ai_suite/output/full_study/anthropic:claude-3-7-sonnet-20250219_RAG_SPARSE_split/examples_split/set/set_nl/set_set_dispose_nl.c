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
predicate nodes(struct node* n; list<void*> values) =
  n == 0 ?
    values == nil
  :
    n->val |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*&
    nodes(next, ?tail) &*& values == cons(v, tail);

// Define a predicate for the set structure
predicate set(struct set* s; list<void*> values) =
  s->head |-> ?head &*& malloc_block_set(s) &*& nodes(head, values);
@*/

/**
 * Description:
 * The set_dispose function disposes of the set by freeing all allocated memory.
 *
 * @param set - A pointer to the set to be disposed of.
 * @requires - The set must be valid.
 * @ensures - All memory associated with the set is freed. 
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