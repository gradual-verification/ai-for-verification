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
predicate nodes(struct node *n, list<void*> vs) =
    n == 0 ?
        vs == nil
    :
        n->val |-> ?v &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        nodes(next, ?rest) &*&
        vs == cons(v, rest);

predicate set(struct set* s, list<void*> vs) =
    s->head |-> ?h &*&
    malloc_block_set(s) &*&
    nodes(h, vs) &*&
    distinct(vs) == true;
@*/

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
    //@ requires set(set, ?values) &*& !mem(x, values);
    //@ ensures set(set, cons(x, values));
{
  //@ open set(set, values);
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
  //@ close nodes(n, cons(x, values));
  //@ close set(set, cons(x, values));
}