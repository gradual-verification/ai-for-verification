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

// We add `distinct(vs)` to the predicate to enforce that the list is a proper set representation.
// This is crucial for proving correctness, especially for `set_add`.
predicate set(struct set* set, int size, fixpoint(void*, bool) elements) =
  set->head |-> ?head &*& malloc_block_set(set) &*& lseg(head, 0, ?vs) &*&
  distinct(vs) == true &*&
  size == length(vs) &*&
  list_as_set(vs) == elements;

// Lemma to connect list membership with set membership for distinct lists.
lemma void distinct_list_as_set_mem(list<void*> vs, void* x)
    requires distinct(vs) == true;
    ensures mem(x, vs) == (list_as_set(vs)(x) == true);
{
    switch(vs) {
        case nil:
        case cons(h, t):
            distinct_list_as_set_mem(t, x);
    }
}

// Lemma to "unroll" one node from a list segment for loop processing.
lemma void lseg_add_node(struct node* first, struct node* last)
    requires lseg(first, last, ?pvs) &*&
             last != 0 &*& last->val |-> ?val &*& last->next |-> ?next &*& malloc_block_node(last) &*&
             lseg(next, 0, ?rvs_tail);
    ensures lseg(first, next, append(pvs, cons(val, nil))) &*& lseg(next, 0, rvs_tail);
{
    open lseg(first, last, pvs);
    if (first == last) {
        close lseg(next, next, nil);
        close lseg(first, next, cons(val, nil));
    } else {
        lseg_add_node(first->next, last);
        close lseg(first, next, append(pvs, cons(val, nil)));
    }
}

// Lemma to join two list segments.
lemma void lseg_append(struct node* n1, struct node* n2)
    requires lseg(n1, n2, ?vs1) &*& lseg(n2, 0, ?vs2);
    ensures lseg(n1, 0, append(vs1, vs2));
{
    open lseg(n1, n2, vs1);
    if (n1 != n2) {
        lseg_append(n1->next, n2);
    }
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
  //@ close set(set, 0, empty_set);
  return set;
}


void set_add(struct set* set, void* x)
//@ requires set(set, ?size, ?elems) &*& elems(x) == false;
//@ ensures set(set, size + 1, fupdate(elems, x, true));
{
  //@ open set(set, size, elems);
  //@ list<void*> vs = ?;
  //@ open lseg(set->head, 0, vs);
  //@ distinct_list_as_set_mem(vs, x);
  //@ assert !mem(x, vs);
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
  //@ close lseg(n, 0, cons(x, vs));
  //@ close set(set, size + 1, fupdate(elems, x, true));
}


bool set_contains(struct set* set, void* x)
//@ requires set(set, ?size, ?elems);
//@ ensures set(set, size, elems) &*& result ? exists<void *>(?elem) &*& elems(elem) == true &*& (uintptr_t)x == (uintptr_t)elem : !elems(x);
{
  //@ open set(set, size, elems);
  //@ list<void*> vs = ?;
  //@ open lseg(set->head, 0, vs);
  //@ distinct_list_as_set_mem(vs, x);
  struct node* curr = set->head;
  bool found = false;
  //@ struct node* head = set->head;
  //@ close lseg(head, curr, nil);
  while(curr != 0 && !found)
    /*@ invariant set->head |-> head &*& malloc_block_set(set) &*&
                  lseg(head, curr, ?pvs) &*& lseg(curr, 0, ?rvs) &*&
                  vs == append(pvs, rvs) &*& distinct(vs) == true &*&
                  size == length(vs) &*& list_as_set(vs) == elems &*&
                  !mem(x, pvs);
    @*/
  {
    //@ open lseg(curr, 0, rvs);
    void* val = curr->val;
    if(val == x) {
      found = true;
    }
    struct node* next = curr->next;
    //@ lseg_add_node(head, curr);
    curr = next;
  }
  
  //@ lseg_append(head, curr);
  //@ if (found) {
  //@     assert mem(x, vs) == true;
  //@ } else {
  //@     assert !mem(x, vs) == true;
  //@ }
  //@ close lseg(head, 0, vs);
  //@ close set(set, size, elems);
  return found;
}


void set_dispose(struct set* set)
//@ requires set(set, ?size, ?elems);
//@ ensures true;
{
  //@ open set(set, size, elems);
  struct node* curr = set->head;
  //@ open lseg(curr, 0, _);
  while(curr != 0)
    //@ invariant lseg(curr, 0, ?vs);
  {
    //@ open lseg(curr, 0, vs);
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