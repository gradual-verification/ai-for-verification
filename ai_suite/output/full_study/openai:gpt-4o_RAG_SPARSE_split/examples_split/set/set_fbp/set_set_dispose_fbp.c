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

//@ predicate node(struct node* n; void* val, struct node* next) = n->val |-> val &*& n->next |-> next &*& malloc_block_node(n);

lemma void lseg_to_nil(struct node* first)
  requires lseg(first, 0, nil);
  ensures first == 0;
{
  open lseg(first, 0, nil);
  if (first != 0) {
    open lseg(first->next, 0, nil);
    lseg_to_nil(first->next);
  }
}

lemma void lseg_to_nodes(struct node* first)
  requires lseg(first, 0, ?vs);
  ensures nodes(first, vs);
{
  open lseg(first, 0, vs);
  if (first != 0) {
    lseg_to_nodes(first->next);
    close nodes(first, vs);
  }
}

lemma void nodes_to_lseg(struct node* first)
  requires nodes(first, ?vs);
  ensures lseg(first, 0, vs);
{
  open nodes(first, vs);
  if (first != 0) {
    nodes_to_lseg(first->next);
    close lseg(first, 0, vs);
  }
}

// TODO: make this function pass the verification
void set_dispose(struct set* set)
//@ requires set(set, ?size, ?elems);
//@ ensures true;
{
  struct node* curr = set->head;
  //@ open set(set, size, elems);
  //@ nodes_to_lseg(curr);
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