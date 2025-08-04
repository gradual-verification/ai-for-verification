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

lemma void lseg_append_node(struct node* first)
    requires lseg(first, ?last, ?vs1) &*& last != 0 &*& last->val |-> ?v &*& last->next |-> ?n &*& lseg(n, 0, ?vs2);
    ensures lseg(first, n, append(vs1, cons(v, nil))) &*& lseg(n, 0, vs2);
{
    open lseg(first, last, vs1);
    if (first != last) {
        lseg_append_node(first->next);
    }
    close lseg(first, n, append(vs1, cons(v, nil)));
}

lemma void lseg_join(struct node* first)
    requires lseg(first, ?mid, ?vs1) &*& lseg(mid, 0, ?vs2);
    ensures lseg(first, 0, append(vs1, vs2));
{
    open lseg(first, mid, vs1);
    if (first != mid) {
        lseg_join(first->next);
        close lseg(first, 0, append(vs1, vs2));
    }
}

lemma void mem_list_as_set(list<void*> vs, void* x)
    requires true;
    ensures mem(x, vs) == ((list_as_set(vs))(x) == true);
{
    switch(vs) {
        case nil:
        case cons(h, t):
            mem_list_as_set(t, x);
    }
}
@*/


// TODO: make this function pass the verification
bool set_contains(struct set* set, void* x)
//@ requires set(set, ?size, ?elems);
//@ ensures set(set, size, elems) &*& result ? elems(x) == true : elems(x) == false;
{
  //@ open set(set, size, elems);
  //@ assert set->head |-> ?head &*& lseg(head, 0, ?vs) &*& list_as_set(vs) == elems;
  struct node* curr = set->head;
  bool found = false;
  //@ close lseg(head, head, nil);
  while(curr != 0 && !found)
  /*@
  invariant
    set->head |-> head &*&
    lseg(head, curr, ?prefix_vs) &*&
    lseg(curr, 0, ?suffix_vs) &*&
    vs == append(prefix_vs, suffix_vs) &*&
    size == length(vs) &*&
    list_as_set(vs) == elems &*&
    found == mem(x, prefix_vs);
  @*/
  {
    //@ open lseg(curr, 0, suffix_vs);
    //@ assert curr->val |-> ?val;
    if(curr->val == x) {
      found = true;
    }
    //@ lseg_append_node(head);
    curr = curr->next;
  }

  //@ lseg_join(head);
  //@ mem_list_as_set(vs, x);
  //@ close set(set, size, elems);
  return found;
}