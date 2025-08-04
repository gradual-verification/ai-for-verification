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
    first != 0 &*&
    first->val |-> ?val &*&
    first->next |-> ?next &*&
    malloc_block_node(first) &*&
    lseg(next, last, ?tail) &*&
    vs == cons(val, tail);

predicate set(struct set* s, int size, fixpoint(void*, bool) elements) =
  s->head |-> ?head &*&
  malloc_block_set(s) &*&
  lseg(head, 0, ?vs) &*&
  size == length(vs) &*&
  list_as_set(vs) == elements;

lemma void mem_list_as_set(list<void*> vs, void* x)
    requires true;
    ensures mem(x, vs) == (list_as_set(vs)(x) == true);
{
    switch (vs) {
        case nil:
        case cons(h, t):
            mem_list_as_set(t, x);
            if (h == x) {} else {}
    }
}

lemma void lseg_add_one(struct node* first, struct node* last)
    requires lseg(first, last, ?pfx) &*& last != 0 &*& last->val |-> ?v &*& last->next |-> ?n &*& malloc_block_node(last);
    ensures lseg(first, n, append(pfx, cons(v, nil)));
{
    open lseg(first, last, pfx);
    if (first == last) {
        close lseg(n, n, nil);
    } else {
        lseg_add_one(first->next, last);
    }
    close lseg(first, n, append(pfx, cons(v, nil)));
}

lemma void lseg_join(struct node* first, struct node* mid)
    requires lseg(first, mid, ?pfx) &*& lseg(mid, 0, ?sfx);
    ensures lseg(first, 0, append(pfx, sfx));
{
    open lseg(first, mid, pfx);
    if (first != mid) {
        lseg_join(first->next, mid);
    }
    close lseg(first, 0, append(pfx, sfx));
}

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
  //@ open set(set, size, elems);
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->val = x;
  n->next = set->head;
  set->head = n;
  //@ assert lseg(n->next, 0, ?vs);
  //@ close lseg(n, 0, cons(x, vs));
  //@ close set(set, size + 1, fupdate(elems, x, true));
}


bool set_contains(struct set* set, void* x)
//@ requires set(set, ?size, ?elems);
//@ ensures set(set, size, elems) &*& result ? elems(x) == true : elems(x) == false;
{
  //@ open set(set, size, elems);
  //@ assert set->head |-> ?head &*& lseg(head, 0, ?vs);
  struct node* curr = set->head;
  bool found = false;
  //@ close lseg(head, head, nil);
  while(curr != 0 && !found)
    //@ invariant lseg(head, curr, ?pfx) &*& lseg(curr, 0, ?sfx) &*& vs == append(pfx, sfx) &*& found == mem(x, pfx);
  {
    //@ open lseg(curr, 0, sfx);
    if(curr->val == x) {
      found = true;
    }
    struct node* next = curr->next;
    //@ lseg_add_one(head, curr);
    curr = next;
  }
  //@ lseg_join(head, curr);
  //@ mem_list_as_set(vs, x);
  //@ if (found) {
  //@     mem_append(x, pfx, sfx);
  //@ } else {
  //@     if (curr == 0) {
  //@         assert pfx == vs;
  //@     }
  //@ }
  //@ close set(set, size, elems);
  return found;
}


void set_dispose(struct set* set)
//@ requires set(set, ?size, ?elems);
//@ ensures true;
{
  //@ open set(set, size, elems);
  struct node* curr = set->head;
  while(curr != 0)
    //@ invariant lseg(curr, 0, _);
  {
    //@ open lseg(curr, 0, _);
    struct node* nxt = curr->next;
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