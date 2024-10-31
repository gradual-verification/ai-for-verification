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
predicate nodes(struct node *n, list<void *> vs) =
  n == 0 ? vs == nil : n->val |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next, ?vs_tail) &*& vs == cons(v, vs_tail);

predicate set(struct set *set, list<void *> vs) =
  set->head |-> ?h &*& malloc_block_set(set) &*& nodes(h, vs) &*& distinct(vs);
@*/

struct set* create_set()
//@ requires true;
//@ ensures result == 0 ? true : set(result, nil);
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
  //@ close set(set, nil);
  return set;
}

void set_add(struct set* set, void* x)
//@ requires set(set, ?vs) &*& mem(x, vs) == false;
//@ ensures set(set, cons(x, vs));
{
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
  //@ close nodes(n, cons(x, vs));
  //@ close set(set, cons(x, vs));
}

bool set_contains(struct set* set, void* x)
//@ requires set(set, ?vs);
//@ ensures set(set, vs) &*& result == mem(x, vs);
{
  struct node* curr = set->head;
  bool found = false;
  //@ open set(set, vs);
  //@ open nodes(curr, vs);
  while(curr != 0) 
  //@ invariant nodes(curr, ?vs_left) &*& found == mem(x, vs) &*& (found ? true : mem(x, vs_left) == false);
  {
    if(curr->val == x) {
      found = true;
    }
    curr = curr->next;
    //@ open nodes(curr, ?vs_tail);
  }
  //@ close set(set, vs);
  return found;
}

void set_dispose(struct set* set)
//@ requires set(set, ?vs);
//@ ensures true;
{
  struct node* curr = set->head;
  //@ open set(set, vs);
  while(curr != 0) 
  //@ invariant nodes(curr, ?vs_remaining);
  {
    struct node* nxt = curr->next;
    free(curr);
    curr = nxt;
  }
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
