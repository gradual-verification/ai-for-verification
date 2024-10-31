```c
#include "stdlib.h"
//@ #include "listex.gh"

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
    first != 0 &*& first->val |-> ?val &*& first->next |-> ?next &*& malloc_block_node(first) &*& lseg(next, last, ?tail) &*& vs == cons(val, tail); 

predicate set(struct set* set, int size, set<void*> elements) =
  set->head |-> ?head &*& malloc_block_set(set) &*& lseg(head, 0, ?vs) &*& size == length(vs) &*& elements == set_of_list(vs);
@*/

struct set* create_set()
//@ requires true;
//@ ensures result == 0 ? true : set(result, 0, empty_set);
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
  //@ close lseg(0, 0, nil);
  //@ close set(set, 0, empty_set);
  return set;
}

void set_add(struct set* set, void* x)
//@ requires set(set, ?size, ?elements) &*& mem(x, elements) == false;
//@ ensures set(set, size + 1, union(elements, singleton_set(x)));
{
  //@ open set(set, size, elements);
  //@ assert set->head |-> ?head &*& malloc_block_set(set) &*& lseg(head, 0, ?vs) &*& size == length(vs) &*& elements == set_of_list(vs);

  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;

  //@ close lseg(n, 0, cons(x, vs));

  //@ elements = set_of_list(vs);
  //@ assert elements == set_of_list(vs);
  //@ elements = set_of_list(vs);
  //@ elements = elements;
  //@ assert union(elements, singleton_set(x)) == set_of_list(cons(x, vs));

  //@ close set(set, size + 1, set_of_list(cons(x, vs)));
}

bool set_contains(struct set* set, void* x)
//@ requires set(set, ?size, ?elements);
//@ ensures set(set, size, elements) &*& result == mem(x, elements);
{
  //@ open set(set, size, elements);
  //@ assert set->head |-> ?head &*& malloc_block_set(set) &*& lseg(head, 0, ?vs) &*& elements == set_of_list(vs);

  struct node* curr = set->head;
  bool found = false;

  //@ list<void*> vs_prefix = nil;
  //@ list<void*> vs_suffix = vs;
  //@ assert vs == append(vs_prefix, vs_suffix);

  while(curr != 0 && !found) 
  /*@
  invariant
    lseg(set->head, curr, vs_prefix)
    &*& lseg(curr, 0, vs_suffix)
    &*& vs == append(vs_prefix, vs_suffix)
    &*& mem(x, set_of_list(vs_prefix)) == false
    &*& malloc_block_set(set)
    &*& found == false;
  @*/
  {
    //@ open lseg(curr, 0, vs_suffix);
    //@ assert curr->val |-> ?curr_val &*& curr->next |-> ?next &*& malloc_block_node(curr) &*& lseg(next, 0, ?vs_rest) &*& vs_suffix == cons(curr_val, vs_rest);

    if(curr->val == x) {
      found = true;
      //@ close lseg(curr, 0, vs_suffix);
    } else {
      //@ vs_prefix = append(vs_prefix, cons(curr_val, nil));
      curr = curr->next;
      //@ vs_suffix = vs_rest;
      //@ close lseg(curr, 0, vs_suffix);
      //@ close lseg(set->head, curr, vs_prefix);
    }
  }

  //@ close lseg(set->head, curr, vs_prefix);
  //@ close lseg(set->head, 0, vs);
  //@ close set(set, size, elements);

  return found;
}

void set_dispose(struct set* set)
//@ requires set(set, ?size, ?elements);
//@ ensures true;
{
  //@ open set(set, size, elements);
  struct node* curr = set->head;
  while(curr != 0)
  //@ invariant lseg(curr, 0, _);
  {
    //@ open lseg(curr, 0, _);
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
```
