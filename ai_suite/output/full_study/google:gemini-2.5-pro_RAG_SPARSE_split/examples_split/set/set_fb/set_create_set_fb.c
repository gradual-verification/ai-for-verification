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
// An lseg (list segment) from `first` to `last`, containing values `vs`.
// NOTE: This predicate was corrected to include `malloc_block_node` to track
// memory ownership, which is crucial for proving memory safety.
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

// A set, represented by a linked list.
// NOTE: This predicate was corrected to include `malloc_block_set` to track
// memory ownership of the main struct.
predicate set(struct set* set, int size, fixpoint(void*, bool) elements) =
  set->head |-> ?head &*&
  malloc_block_set(set) &*&
  lseg(head, 0, ?vs) &*&
  size == length(vs) &*&
  list_as_set(vs) == elements;
@*/


// TODO: make this function pass the verification
struct set* create_set()
//@ requires true;
//@ ensures result == 0 ? true : set(result, 0, (empty_set));
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
 
  // To prove the postcondition, we must construct the `set` predicate.
  // First, we establish the `lseg` for an empty list, which starts and ends at null.
  //@ close lseg(0, 0, nil);
  
  // Now, we have all the necessary components to form the `set` predicate:
  // - `set->head |-> 0` (from the assignment)
  // - `malloc_block_set(set)` (from malloc)
  // - `lseg(0, 0, nil)` (which we just closed)
  // The logical properties `length(nil) == 0` and `list_as_set(nil) == empty_set` also hold.
  //@ close set(set, 0, (empty_set));
  
  return set;
}