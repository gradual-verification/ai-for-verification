```c
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
  //@ close set(set, 0, (empty_set));
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
  //@ open set(set, size, elems);
  //@ list<void*> vs = ?vs;
  //@ close lseg(n, 0, cons(x, vs));
  set->head = n;
  //@ close set(set, size + 1, fupdate(elems, x, true));
}

bool set_contains(struct set* set, void* x)
//@ requires set(set, ?size, ?elems);
//@ ensures set(set, size, elems) &*& result == elems(x);
{
  //@ open set(set, size, elems);
  struct node* curr = set->head;
  bool found = false;
  //@ list<void*> vs = ?vs;
  //@ list<void*> vs_traversed = nil;
  //@ list<void*> vs_rest = vs;
  
  while(curr != 0 && !found)
  /*@
  invariant lseg(set->head, curr, vs_traversed) &*& lseg(curr, 0, vs_rest) &*& vs == append(vs_traversed, vs_rest) &*& found == mem(x, vs_traversed);
  @*/
  {
    //@ open lseg(curr, 0, vs_rest);
    //@ curr->val |-> ?v &*& curr->next |-> ?next &*& lseg(next, 0, ?vs_rest_rest) &*& vs_rest == cons(v, vs_rest_rest);
    if(curr->val == x) {
      found = true;
    }
    curr = curr->next;
    //@ vs_traversed = append(vs_traversed, cons(v, nil));
    //@ vs_rest = vs_rest_rest;
    //@ close lseg(curr, 0, vs_rest);
  }
  //@ close lseg(set->head, curr, vs_traversed);
  //@ close lseg(curr, 0, vs_rest);
  //@ close set(set, size, elems);
  //@ assert result == elems(x);
  return found;
}

void set_dispose(struct set* set)
//@ requires set(set, ?size, ?elems);
//@ ensures true;
{
  //@ open set(set, size, elems);
  struct node* curr = set->head;
  //@ list<void*> vs = ?vs;
  //@ open lseg(curr, 0, vs);
  while(curr != 0) 
  /*@
  invariant lseg(curr, 0, ?vs_rest);
  @*/
  {
    //@ open lseg(curr, 0, vs_rest);
    struct node* nxt = curr->next;
    //@ curr->val |-> _; curr->next |-> _;
    free(curr);
    curr = nxt;
    //@ vs_rest = tail(vs_rest);
    //@ close lseg(curr, 0, vs_rest);
  }
  //@ close lseg(0, 0, nil);
  free(set);
}


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
```
