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
    first->val |-> ?val &*& first->next |-> ?next &*& malloc_block_node(first) &*& lseg(next, last, ?tail) &*& vs == cons(val, tail); 

predicate set(struct set* set, int size, fixpoint(void*, bool) elements) =
  set->head |-> ?head &*& malloc_block_set(set) &*& lseg(head, 0, ?vs) &*& size == length(vs) &*& list_as_set(vs) == elements;
@*/


// TODO: make this function pass the verification
void set_dispose(struct set* set)
//@ requires set(set, ?size, ?elems);
//@ ensures true;
{
  //@ open set(set, size, elems);
  struct node* curr = set->head;
  //@ open lseg(curr, 0, _);
  while(curr != 0) 
  //@ invariant curr == 0 ? true : lseg(curr, 0, ?vs);
  {
    struct node* nxt = curr->next;
    //@ open lseg(curr, 0, vs);
    free(curr);
    curr = nxt;
    //@ if (curr != 0) open lseg(curr, 0, tail(vs));
  }
  free(set);
}