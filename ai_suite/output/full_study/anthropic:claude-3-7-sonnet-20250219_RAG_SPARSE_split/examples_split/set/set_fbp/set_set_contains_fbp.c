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

lemma void lseg_to_lseg_with_elem(struct node* first, struct node* last, void* x)
  requires lseg(first, last, ?vs);
  ensures lseg(first, last, vs) &*& mem(x, vs) ? exists<void*>(x) &*& list_as_set(vs)(x) == true : !list_as_set(vs)(x);
{
  open lseg(first, last, vs);
  if (first != last) {
    if (first->val == x) {
      close exists(x);
    } else {
      lseg_to_lseg_with_elem(first->next, last, x);
    }
  }
  close lseg(first, last, vs);
}
@*/

bool set_contains(struct set* set, void* x)
//@ requires set(set, ?size, ?elems);
//@ ensures set(set, size, elems) &*& result ? exists<void *>(?elem) &*& elems(elem) == true &*& (uintptr_t)x == (uintptr_t)elem : !elems(x);
{
  //@ open set(set, size, elems);
  struct node* curr = set->head;
  bool found = false;
  
  //@ lseg_to_lseg_with_elem(curr, 0, x);
  
  while(curr != 0 && !found) 
  //@ invariant lseg(set->head, curr, ?vs1) &*& lseg(curr, 0, ?vs2) &*& !found &*& list_as_set(append(vs1, vs2)) == elems &*& length(append(vs1, vs2)) == size;
  {
    //@ open lseg(curr, 0, vs2);
    if(curr->val == x) {
      found = true;
      //@ close exists(curr->val);
    }
    curr = curr->next;
    //@ close lseg(curr, 0, tail(vs2));
    //@ close lseg(set->head, curr, append(vs1, cons(head(vs2), nil)));
  }
  
  //@ close set(set, size, elems);
  return found;
}