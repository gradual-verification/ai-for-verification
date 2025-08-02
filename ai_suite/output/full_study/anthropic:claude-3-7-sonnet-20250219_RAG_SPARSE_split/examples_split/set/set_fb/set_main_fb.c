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


struct set* create_set()
//@ requires true;
//@ ensures result == 0 ? true : set(result, 0, (empty_set));
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
 
  //@ close lseg(0, 0, nil);
  //@ close set(set, 0, empty_set);
  return set;
}


void set_add(struct set* set, void* x)
//@ requires set(set, ?size, ?elems) &*& elems(x) == false;
//@ ensures set(set, size + 1, fupdate(elems, x, true));
{
  //@ open set(set, size, elems);
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
  
  //@ close lseg(n, 0, cons(x, ?vs));
  //@ close set(set, size + 1, fupdate(elems, x, true));
}


bool set_contains(struct set* set, void* x)
//@ requires set(set, ?size, ?elems);
//@ ensures set(set, size, elems) &*& result ? elems(x) == true : elems(x) == false;
{
  //@ open set(set, size, elems);
  struct node* curr = set->head;
  bool found = false;
  //@ list<void*> vs_orig = ?vs;
  //@ close lseg(curr, 0, vs);
  
  while(curr != 0 && !found) 
  //@ invariant lseg(curr, 0, ?vs_curr) &*& !found ? true : mem(x, vs_curr);
  {
    //@ open lseg(curr, 0, vs_curr);
    if(curr->val == x) {
      found = true;
    }
    curr = curr->next;
    //@ if (!found) close lseg(curr, 0, ?tail);
    //@ else close lseg(curr, 0, ?tail);
  }
  
  //@ close set(set, size, elems);
  return found;
}


void set_dispose(struct set* set)
//@ requires set(set, ?size, ?elems);
//@ ensures true;
{
  //@ open set(set, size, elems);
  struct node* curr = set->head;
  //@ open lseg(curr, 0, ?vs);
  
  while(curr != 0) 
  //@ invariant lseg(curr, 0, ?vs_curr);
  {
    //@ open lseg(curr, 0, vs_curr);
    struct node* nxt = curr->next;
    free(curr);
    curr = nxt;
    //@ if (curr != 0) open lseg(curr, 0, ?tail);
  }
  
  free(set);
}



int main() //@ : main
//@ requires true;
//@ ensures true;
{
  struct set* set = create_set();
  if(set == 0) return 0;
  
  //@ assert set(set, 0, empty_set);
  //@ assert empty_set((void*) 1) == false;
  set_add(set, (void*) 1);
  
  //@ assert set(set, 1, fupdate(empty_set, (void*) 1, true));
  //@ assert fupdate(empty_set, (void*) 1, true)((void*) 2) == false;
  set_add(set, (void*) 2);
  
  //@ assert set(set, 2, fupdate(fupdate(empty_set, (void*) 1, true), (void*) 2, true));
  //@ assert fupdate(fupdate(empty_set, (void*) 1, true), (void*) 2, true)((void*) 3) == false;
  set_add(set, (void*) 3);
  
  //@ assert set(set, 3, fupdate(fupdate(fupdate(empty_set, (void*) 1, true), (void*) 2, true), (void*) 3, true));
  //@ assert fupdate(fupdate(fupdate(empty_set, (void*) 1, true), (void*) 2, true), (void*) 3, true)((void*) 1) == true;
  bool cnt = set_contains(set, (void*) 1);
  assert(cnt);
  
  set_dispose(set);
  return 0;
}