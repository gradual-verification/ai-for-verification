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

lemma void list_as_set_is_mem<t>(list<t> l, t x)
    requires true;
    ensures list_as_set(l)(x) == mem(x, l);
{
    switch(l) {
        case nil:
        case cons(h, t):
            list_as_set_is_mem(t, x);
    }
}

lemma void lseg_append_val(struct node* first, struct node* last)
    requires lseg(first, last, ?p_vs) &*&
             last != 0 &*& last->val |-> ?val &*& last->next |-> ?next &*& malloc_block_node(last) &*&
             lseg(next, 0, ?r_vs);
    ensures lseg(first, next, append(p_vs, cons(val, nil))) &*& lseg(next, 0, r_vs);
{
    open lseg(first, last, p_vs);
    if (first == last) {
        close lseg(next, next, nil);
    } else {
        lseg_append_val(first->next, last);
    }
    open lseg(next, 0, r_vs);
    close lseg(next, 0, r_vs);
    close lseg(first, next, append(p_vs, cons(val, nil)));
}

lemma void lseg_join(struct node* n1, struct node* n2)
    requires lseg(n1, n2, ?vs1) &*& lseg(n2, 0, ?vs2);
    ensures lseg(n1, 0, append(vs1, vs2));
{
    open lseg(n1, n2, vs1);
    if (n1 != n2) {
        lseg_join(n1->next, n2);
        close lseg(n1, 0, append(vs1, vs2));
    }
}
@*/


// TODO: make this function pass the verification
bool set_contains(struct set* set, void* x)
//@ requires set(set, ?size, ?elems);
//@ ensures set(set, size, elems) &*& result ? exists<void *>(?elem) &*& elems(elem) == true &*& (uintptr_t)x == (uintptr_t)elem : !elems(x);
{
  //@ open set(set, size, elems);
  //@ assert set->head |-> ?head &*& lseg(head, 0, ?vs) &*& list_as_set(vs) == elems;
  struct node* curr = set->head;
  bool found = false;
  //@ close lseg(head, head, nil);
  //@ list<void*> p_vs = nil;
  while(curr != 0 && !found)
  /*@
  invariant set->head |-> head &*& malloc_block_set(set) &*&
            lseg(head, curr, p_vs) &*& lseg(curr, 0, ?r_vs) &*&
            vs == append(p_vs, r_vs) &*&
            found == mem(x, p_vs) &*&
            size == length(vs) &*& list_as_set(vs) == elems;
  @*/
  {
    //@ open lseg(curr, 0, r_vs);
    //@ void* val = curr->val;
    if(curr->val == x) {
      found = true;
    }
    //@ struct node* next = curr->next;
    //@ lseg_append_val(head, curr);
    //@ list<void*> old_p_vs = p_vs;
    //@ p_vs = append(p_vs, cons(val, nil));
    curr = curr->next;
    //@ if (val == x) {
    //@   mem_append(x, old_p_vs, cons(val, nil));
    //@ } else {
    //@   mem_append(x, old_p_vs, cons(val, nil));
    //@ }
  }

  //@ lseg_join(head, curr);
  //@ list_as_set_is_mem(vs, x);
  //@ if (found) {
  //@   mem_append(x, p_vs, r_vs);
  //@   close exists(x);
  //@ } else {
  //@   assert curr == 0;
  //@   open lseg(0, 0, r_vs);
  //@   append_nil(p_vs);
  //@   assert !mem(x, p_vs);
  //@   assert !mem(x, vs);
  //@ }
  //@ close set(set, size, elems);
  return found;
}