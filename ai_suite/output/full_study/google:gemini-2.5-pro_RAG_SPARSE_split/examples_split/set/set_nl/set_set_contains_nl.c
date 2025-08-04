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
// A predicate for a list segment from `from` to `to`.
// It models the sequence of nodes as a logical list of values `vs`.
predicate lseg(struct node* from, struct node* to, list<void*> vs) =
    from == to ?
        vs == nil
    :
        from != 0 &*&
        from->val |-> ?v &*&
        from->next |-> ?next &*&
        malloc_block_node(from) &*&
        lseg(next, to, ?tvs) &*&
        vs == cons(v, tvs);

// A predicate for the set data structure.
// It holds the head of the list and an `lseg` for the entire list.
predicate set_pred(struct set* s, list<void*> vs) =
    s->head |-> ?h &*&
    malloc_block_set(s) &*&
    lseg(h, 0, vs);

// A lemma to prove that two adjacent list segments can be joined.
lemma void lseg_append(struct node* n1, struct node* n2, struct node* n3, list<void*> vs1, list<void*> vs2)
    requires lseg(n1, n2, vs1) &*& lseg(n2, n3, vs2);
    ensures lseg(n1, n3, append(vs1, vs2));
{
    open lseg(n1, n2, vs1);
    if (n1 != n2) {
        lseg_append(n1->next, n2, n3, tail(vs1), vs2);
        close lseg(n1, n3, append(vs1, vs2));
    }
}
@*/


// TODO: make this function pass the verification
/***
 * Description: 
The set_contains function checks whether a given element is present in the set.

@param set - A pointer to the set.
@param x - A pointer to the element to check for.
@ensures - Returns true if x is present in the set, otherwise returns false. The set remains unchanged.
*/
bool set_contains(struct set* set, void* x)
    //@ requires [?f]set_pred(set, ?vs);
    //@ ensures [f]set_pred(set, vs) &*& result == mem(x, vs);
{
  //@ open [f]set_pred(set, vs);
  //@ assert [f]set->head |-> ?h &*& [f]malloc_block_set(set) &*& lseg(h, 0, vs);
  struct node* curr = set->head;
  bool found = false;
  
  //@ close lseg(h, h, nil);
  //@ list<void*> p_vs = nil;
  
  while(curr != 0 && !found)
    /*@ invariant [f]set->head |-> h &*& [f]malloc_block_set(set) &*&
                  lseg(h, curr, p_vs) &*& lseg(curr, 0, ?s_vs) &*&
                  vs == append(p_vs, s_vs) &*&
                  (found ? mem(x, p_vs) : !mem(x, p_vs));
    @*/
  {
    //@ open lseg(curr, 0, s_vs);
    //@ assert curr->val |-> ?v;
    
    if(curr->val == x) {
      found = true;
    }
    
    struct node* next = curr->next;
    
    // Re-establish the invariant for the next iteration.
    //@ close lseg(curr, next, cons(v, nil));
    //@ lseg_append(h, curr, next, p_vs, cons(v, nil));
    //@ p_vs = append(p_vs, cons(v, nil));
    //@ append_assoc(p_vs, cons(v, nil), tail(s_vs));
    
    curr = next;
  }
  
  // After the loop, restore the full `set_pred` predicate.
  //@ assert lseg(h, curr, p_vs) &*& lseg(curr, 0, ?s_vs);
  //@ lseg_append(h, curr, 0, p_vs, s_vs);
  //@ close [f]set_pred(set, vs);
  
  /*@
  // Prove the postcondition about the return value.
  if (found) {
      // Loop terminated because `found` became true.
      // The invariant `mem(x, p_vs)` holds.
      // `mem(x, p_vs)` implies `mem(x, vs)`.
      mem_append(x, p_vs, s_vs);
  } else {
      // Loop terminated because `curr == 0`.
      // This means `s_vs` is `nil`, so `vs == p_vs`.
      // The invariant `!mem(x, p_vs)` holds, so `!mem(x, vs)`.
  }
  @*/
  
  return found;
}