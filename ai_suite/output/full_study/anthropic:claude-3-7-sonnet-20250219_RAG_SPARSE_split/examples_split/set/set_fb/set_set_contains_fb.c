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

bool set_contains(struct set* set, void* x)
//@ requires set(set, ?size, ?elems);
//@ ensures set(set, size, elems) &*& result ? elems(x) == true : elems(x) == false;
{
  //@ open set(set, size, elems);
  struct node* curr = set->head;
  bool found = false;
  
  /*@
  predicate nodes_ahead(struct node* curr, list<void*> vs) =
    lseg(curr, 0, vs);
  @*/
  
  //@ list<void*> vs;
  //@ assert lseg(curr, 0, vs);
  
  while(curr != 0 && !found) 
  //@ invariant nodes_ahead(curr, ?remaining) &*& found ? mem(x, vs) == true : true;
  {
    //@ open nodes_ahead(curr, remaining);
    //@ open lseg(curr, 0, remaining);
    if(curr->val == x) {
      found = true;
      //@ assert mem(x, remaining) == true;
      //@ assert mem(x, vs) == true;
    }
    curr = curr->next;
    //@ close nodes_ahead(curr, tail(remaining));
  }
  
  //@ open nodes_ahead(curr, _);
  
  /*@
  if (found) {
    assert mem(x, vs) == true;
    assert list_as_set(vs)(x) == true;
    assert elems(x) == true;
  } else {
    assert curr == 0;
    assert !mem(x, vs);
    assert list_as_set(vs)(x) == false;
    assert elems(x) == false;
  }
  @*/
  
  //@ close set(set, size, elems);
  return found;
}