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
predicate nodes(struct node* node; list<void*> vs) =
  node == 0 ?
    vs == nil
  :
    node->val |-> ?v &*& node->next |-> ?next &*&
    malloc_block_node(node) &*&
    nodes(next, ?next_vs) &*&
    vs == cons(v, next_vs);

predicate set(struct set* set, int size, fixpoint(void*, bool) elements) =
  set->head |-> ?head &*& nodes(head, ?vs) &*&
  malloc_block_set(set) &*&
  size == length(vs) &*&
  list_as_set(vs) == elements;
@*/

struct set* create_set()
//@ requires true;
//@ ensures result == 0 ? true : set(result, 0, (empty_set));
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
  //@ close nodes(0, nil);
  //@ close set(set, 0, (empty_set));
  return set;
}

void set_add(struct set* set, void* x)
//@ requires set(set, ?size, ?elems) &*& elems(x) == false;
//@ ensures set(set, size + 1, fupdate(elems, x, true));
{
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->val = x;
  n->next = set->head;
  set->head = n;
  //@ close nodes(n, cons(x, ?tail_vs));
  //@ open set(set, size, elems);
  //@ close set(set, size + 1, fupdate(elems, x, true));
}

bool set_contains(struct set* set, void* x)
//@ requires set(set, ?size, ?elems);
//@ ensures set(set, size, elems) &*& result ? elems(x) == true : elems(x) == false;
{
  struct node* curr = set->head;
  bool found = false;
  //@ open set(set, size, elems);
  //@ open nodes(curr, _);
  while(curr != 0 && !found) 
  //@ invariant nodes(curr, ?curr_vs);
  {
    if(curr->val == x) {
      found = true;
    }
    curr = curr->next;
    //@ open nodes(curr, _);
  }
  //@ close nodes(curr, _);
  //@ close set(set, size, elems);
  return found;
}

void set_dispose(struct set* set)
//@ requires set(set, ?size, ?elems);
//@ ensures true;
{
  struct node* curr = set->head;
  while(curr != 0) 
  //@ invariant nodes(curr, _);
  {
    struct node* nxt = curr->next;
    //@ open nodes(curr, _);
    free(curr);
    curr = nxt;
  }
  //@ open nodes(0, _);
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
