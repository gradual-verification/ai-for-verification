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
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
  //@ close lseg(n, 0, cons(x, ?vs));
  //@ open set(set, size, elems);
  //@ close set(set, size + 1, fupdate(elems, x, true));
}

bool set_contains(struct set* set, void* x)
//@ requires set(set, ?size, ?elems);
//@ ensures set(set, size, elems) &*& result ? exists<void *>(?elem) &*& elems(elem) == true &*& (uintptr_t)x == (uintptr_t)elem : !elems(x);
{
  struct node* curr = set->head;
  bool found = false;
  while(curr != 0 && ! found) 
  //@ invariant lseg(set->head, curr, ?vs) &*& lseg(curr, 0, ?rest) &*& set(set, size, elems) &*& found == (exists<void *>(?elem) &*& elems(elem) == true &*& (uintptr_t)x == (uintptr_t)elem);
  {
    //@ open lseg(curr, 0, rest);
    if(curr->val == x) {
      found = true;
    }
    curr = curr->next;
  }
  //@ close lseg(curr, 0, rest);
  return found;
}

void set_dispose(struct set* set)
//@ requires set(set, ?size, ?elems);
//@ ensures true;
{
  struct node* curr = set->head;
  while(curr != 0) 
  //@ invariant lseg(curr, 0, ?vs);
  {
    struct node* nxt = curr->next;
    //@ open lseg(curr, 0, vs);
    free(curr);
    curr = nxt;
  }
  //@ open lseg(0, 0, _);
  free(set);
}

// TODO: make this function pass the verification
int main() //@ : main
//@ requires true;
//@ ensures true;
{
  struct set* set = create_set();
  if(set == 0) return 0;
  set_add(set, (void*) 1);
  set_add(set, (void*) 2);
  set_add(set, (void*) 3);
  bool cnt = set_contains(set, (void*) 1);
  assert(cnt);
  set_dispose(set);
  return 0;
}