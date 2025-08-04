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
// Predicate for a linked list of nodes.
// It represents the list starting at 'n' as a ghost list of values 'vs'.
predicate nodes(struct node* n, list<void*> vs) =
    n == 0 ?
        // An empty list of nodes corresponds to an empty ghost list.
        vs == nil
    :
        // A non-empty list owns the current node's fields and the rest of the list.
        n->val |-> ?v &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        nodes(next, ?rest) &*&
        vs == cons(v, rest);

// Predicate for a set structure.
// It represents the set 's' as containing a list of elements 'elems'.
predicate set_predicate(struct set* s, list<void*> elems) =
    s->head |-> ?h &*&
    malloc_block_set(s) &*&
    nodes(h, elems);
@*/


// TODO: make this function pass the verification
/*** 
 * Description:
The create_set function creates a new, empty set.

@param - None.
@requires - No specific preconditions.
@ensures - Returns a pointer to a newly allocated set if successful, or 0. The set is initially empty.
*/
struct set* create_set()
    //@ requires true;
    //@ ensures result == 0 ? emp : set_predicate(result, nil);
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  
  // Initialize the head of the new set to NULL, making it empty.
  set->head = 0;
  
  // Prove that the initialized structure represents an empty set.
  // An empty list of nodes (from head=0) corresponds to an empty ghost list (nil).
  //@ close nodes(0, nil);
  // Now, we can establish the predicate for the set itself.
  //@ close set_predicate(set, nil);
  
  return set;
}