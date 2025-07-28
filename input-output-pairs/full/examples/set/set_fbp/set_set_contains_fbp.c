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
bool set_contains(struct set* set, void* x)
//@ requires set(set, ?size, ?elems);
//@ ensures set(set, size, elems) &*& result ? exists<void *>(?elem) &*& elems(elem) == true &*& (uintptr_t)x == (uintptr_t)elem : !elems(x);
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

