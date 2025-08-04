#include "stdlib.h"
#include "assert.h"
//@ #include "maps.gh"
//@ #include "list.gh"

/*@
// Predicate for a list of nodes from 'n' to null.
predicate nodes(struct node* n, list<void*> vs) =
    n == 0 ?
        vs == nil
    :
        n->val |-> ?v &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        nodes(next, ?rest) &*&
        vs == cons(v, rest);

// Predicate for a list segment from 'from' to 'to'.
predicate lseg(struct node* from, struct node* to, list<void*> vs) =
    from == to ?
        vs == nil
    :
        from != 0 &*&
        from->val |-> ?v &*&
        from->next |-> ?next &*&
        malloc_block_node(from) &*&
        lseg(next, to, ?rest) &*&
        vs == cons(v, rest);

// Predicate for the set data structure.
// It owns the set struct and the list of nodes.
// It also specifies that the list of values must be distinct.
predicate set(struct set* s, list<void*> vs) =
    s->head |-> ?h &*&
    malloc_block_set(s) &*&
    nodes(h, vs) &*&
    distinct(vs) == true;

// Lemma to convert a 'nodes' predicate to an 'lseg' predicate ending at null.
lemma void nodes_to_lseg(struct node* n)
    requires nodes(n, ?vs);
    ensures lseg(n, 0, vs);
{
    open nodes(n, vs);
    if (n != 0) {
        nodes_to_lseg(n->next);
    }
    close lseg(n, 0, vs);
}

// Lemma to convert an 'lseg' predicate ending at null back to a 'nodes' predicate.
lemma void lseg_to_nodes(struct node* n)
    requires lseg(n, 0, ?vs);
    ensures nodes(n, vs);
{
    open lseg(n, 0, vs);
    if (n != 0) {
        lseg_to_nodes(n->next);
    }
    close nodes(n, vs);
}

// Lemma to extend a list segment by one node.
// This is useful for loop invariants when iterating through a list.
lemma void lseg_add(struct node* from, struct node* to)
    requires [?f]lseg(from, to, ?vs1) &*& [f]to->val |-> ?v &*& [f]to->next |-> ?next &*& [f]malloc_block_node(to);
    ensures [f]lseg(from, next, append(vs1, cons(v, nil)));
{
    open [f]lseg(from, to, vs1);
    if (from != to) {
        lseg_add(from->next, to);
    }
    close [f]lseg(from, next, append(vs1, cons(v, nil)));
}

@*/

struct node {
  void* val;
  struct node* next;
};

struct set {
  struct node* head;
};


/*** 
 * Description:
The create_set function creates a new, empty set.

@param - None.
@requires - No specific preconditions.
@ensures - Returns a pointer to a newly allocated set if successful, or 0. The set is initially empty.
*/
struct set* create_set()
    //@ requires true;
    //@ ensures result == 0 ? true : set(result, nil);
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
  //@ close nodes(0, nil);
  //@ close set(set, nil);
  return set;
}


/*** 
 * Description:
The set_add function adds a new element to the set.

@param set - A pointer to the set.
@param x - A pointer to the element to be added.
@requires - The set must be valid and x must not already be in the set.
@ensures - The set is updated to include x, and the size of the set is incremented by one.
*/
void set_add(struct set* set, void* x)
    //@ requires set(set, ?vs) &*& !mem(x, vs);
    //@ ensures set(set, cons(x, vs));
{
  //@ open set(set, vs);
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
  //@ close nodes(n, cons(x, vs));
  //@ close set(set, cons(x, vs));
}


/***
 * Description: 
The set_contains function checks whether a given element is present in the set.

@param set - A pointer to the set.
@param x - A pointer to the element to check for.
@ensures - Returns true if x is present in the set, otherwise returns false. The set remains unchanged.
*/
bool set_contains(struct set* set, void* x)
    //@ requires [?f]set(set, ?vs);
    //@ ensures [f]set(set, vs) &*& result == mem(x, vs);
{
  //@ open set(set, vs);
  //@ nodes_to_lseg(set->head);
  struct node* curr = set->head;
  bool found = false;
  //@ close [f]lseg(set->head, set->head, nil);
  while(curr != 0 && ! found)
    /*@ invariant [f]set->head |-> ?h &*& h == set->head &*& [f]malloc_block_set(set) &*&
                  [f]lseg(h, curr, ?seen) &*& [f]lseg(curr, 0, ?rest) &*&
                  vs == append(seen, rest) &*& distinct(vs) == true &*&
                  (found ? mem(x, seen) : !mem(x, seen));
    @*/
  {
    //@ open [f]lseg(curr, 0, rest);
    if(curr->val == x) {
      found = true;
    }
    struct node* next = curr->next;
    //@ lseg_add(set->head, curr);
    curr = next;
    /*@ list<void*> old_seen = seen;
        list<void*> old_rest = rest;
        if (found) {
            mem_append(x, old_seen, cons(head(old_rest), nil));
        } else {
            if (head(old_rest) != x)
                not_mem_append(x, old_seen, cons(head(old_rest), nil));
            else
                assert false;
        }
    @*/
  }
  /*@
    if (found) {
        mem_append(x, seen, rest);
    } else {
        if (curr == 0) {
            assert rest == nil;
            append_nil(seen);
            assert seen == vs;
            assert !mem(x, vs);
        } else { // found is true, impossible
            assert false;
        }
    }
    open [f]lseg(0, 0, _);
    lseg_to_nodes(set->head);
    close [f]set(set, vs);
  @*/
  return found;
}


/***
 * Description:
The set_dispose function disposes of the set by freeing all allocated memory.

@param set - A pointer to the set to be disposed of.
@requires - The set must be valid.
@ensures - All memory associated with the set is freed. 
*/
void set_dispose(struct set* set)
    //@ requires set(set, ?vs);
    //@ ensures true;
{
  //@ open set(set, vs);
  struct node* curr = set->head;
  while(curr != 0)
    //@ invariant nodes(curr, _);
  {
    //@ open nodes(curr, _);
    struct node* nxt = curr->next;
    free(curr);
    curr = nxt;
  }
  //@ open nodes(0, _);
  free(set);
}


// TODO: make this function pass the verification
/***
* Description:
The main function demonstrates the use of the set data structure.
*/
int main() 
    //@ requires true;
    //@ ensures true;
{
  struct set* set = create_set();
  if(set == 0) return 0;
  
  set_add(set, (void*) 1);
  //@ assert set(set, cons((void*)1, nil));
  
  set_add(set, (void*) 2);
  //@ assert set(set, cons((void*)2, cons((void*)1, nil)));
  
  set_add(set, (void*) 3);
  //@ list<void*> vs = cons((void*)3, cons((void*)2, cons((void*)1, nil)));
  //@ assert set(set, vs);
  
  bool cnt = set_contains(set, (void*) 1);
  //@ assert set(set, vs) &*& cnt == mem((void*)1, vs);
  //@ assert cnt == true;
  assert(cnt);
  
  set_dispose(set);
  return 0;
}