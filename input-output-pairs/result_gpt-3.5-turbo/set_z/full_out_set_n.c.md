```c CODE and SPEC
#include "stdlib.h"

struct node {
  void* val;
  struct node* next;
};

struct set {
  struct node* head;
};

/*@

predicate nodes(struct node* node, list<void*> values) =
  node == 0 ?
    values == nil
  :
    node->val |-> ?val &*& node->next |-> ?next &*&
    malloc_block_node(node) &*& nodes(next, ?values0) &*&
    values == cons(val, values0);

predicate set(struct set* set, list<void*> elements) =
  set == 0 ? true : set->head |-> ?head &*& malloc_block_set(set) &*& nodes(head, ?values) &*& elements == values;

@*/

struct set* create_set()
  //@ requires emp;
  //@ ensures result == 0 ? emp : set(result, nil);
{
  struct set* set = malloc(sizeof(struct set));
  if (set == 0) return 0;
  set->head = 0;
  //@ close nodes(0, nil);
  //@ close set(set, nil);
  return set;
}

void set_add(struct set* set, void* x)
  //@ requires set(set, ?elements) &*& !mem(x, elements);
  //@ ensures set(set, cons(x, elements));
{
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->val = x;
  n->next = set->head;
  set->head = n;
  //@ close nodes(n, cons(x, elements));
  //@ close set(set, _);
}

bool set_contains(struct set* set, void* x)
  //@ requires set(set, ?elements);
  //@ ensures set(set, elements) &*& result ? mem(x, elements) : !mem(x, elements);
{
  struct node* curr = set->head;
  bool found = false;
  while(curr != 0 && !found)
    //@ invariant nodes(curr, ?values) &*& set->head |-> curr &*& set(set, values) &*& !found ? !mem(x, values) : mem(x, values);
  {
    if(curr->val == x) {
      found = true;
    }
    curr = curr->next;
  }
  //@ close set(set, values);
  return found;
}

void set_dispose(struct set* set)
  //@ requires set(set, ?elements);
  //@ ensures emp;
{
  struct node* curr = set->head;
  while(curr != 0)
    //@ invariant nodes(curr, ?values) &*& set->head |-> curr &*& set(set, values);
  {
    struct node* nxt = curr->next;
    free(curr);
    curr = nxt;
  }
  free(set);
}

int main() 
  //@ requires emp;
  //@ ensures emp;
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
