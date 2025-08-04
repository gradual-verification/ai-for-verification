#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};

// specific to cell

struct cell {
  int val;
};

/*@
// A predicate to represent a singly-linked list of nodes.
// 'n' is a pointer to the head of the list.
// 'vs' is a ghost list (a pure model) of the values stored in the linked list.
// The type of the values is `void *`, matching the `value` field of `struct node`.
predicate nodes(struct node *n; list<void *> vs) =
    // Base case: If the pointer 'n' is null, the list is empty.
    // The ghost list 'vs' must be 'nil'.
    n == 0 ?
        vs == nil
    :
        // Recursive case: If 'n' is not null, it must point to a valid node.
        // We must have ownership of the 'value' and 'next' fields.
        n->value |-> ?v &*&
        n->next |-> ?next &*&
        // We must have ownership of the memory block for the node itself.
        malloc_block_node(n) &*&
        // The 'next' pointer must point to a valid list segment.
        nodes(next, ?tail) &*&
        // The ghost list 'vs' is constructed by prepending the current node's
        // value 'v' to the ghost list of the rest of the list ('tail').
        vs == cons(v, tail);
@*/


// TODO: make this function pass the verification
/*create_list() function
-params: none
-description: creates an empty list*/
struct node* create_list()
    //@ requires true;
    //@ ensures nodes(result, nil);
{
  return 0;
}