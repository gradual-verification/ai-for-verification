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
    first->val |-> ?val &*& first->next |-> ?next &*& lseg(next, last, ?tail) &*& vs == cons(val, tail);

predicate set(struct set* set, int size, fixpoint(void*, bool) elements) =
  set->head |-> ?head &*& lseg(head, 0, ?vs) &*& size == length(vs) &*& list_as_set(vs) == elements;
@*/


// TODO: make this function pass the verification
void set_dispose(struct set* set)
//@ requires set(set, ?size, ?elems);
//@ ensures true;
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


