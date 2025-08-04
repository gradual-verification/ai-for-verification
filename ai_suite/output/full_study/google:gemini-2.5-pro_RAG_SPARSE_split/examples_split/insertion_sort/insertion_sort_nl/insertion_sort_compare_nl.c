#include "prelude.h"

// Definition of a singly linked list node holding an integer value
struct list_node {
  int value;
  struct list_node* next;
};

/*@
// A predicate to represent ownership of a single list_node struct.
// It takes the node pointer 'n', and ghost parameters for its 'value' and 'next' fields.
predicate list_node(struct list_node *n; int value, struct list_node *next) =
    // We have permission to access the 'value' field, and its value is the ghost parameter 'value'.
    n->value |-> value &*&
    // We have permission to access the 'next' field, and its value is the ghost parameter 'next'.
    n->next |-> next &*&
    // We own the memory block for the struct itself.
    malloc_block_list_node(n);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The compare function compares the integer values of two linked list nodes.

@param n0 - pointer to the first node.
@param n1 - pointer to the second node.
@return -1 if n0's value < n1's value,
 *          1 if n0's value > n1's value,
 *          0 if equal.

It also makes sure that the values of the nodes are not modified during comparison.
*/
static int compare(struct list_node* n0, struct list_node* n1)
    //@ requires list_node(n0, ?v0, ?next0) &*& list_node(n1, ?v1, ?next1);
    /*@ ensures list_node(n0, v0, next0) &*& list_node(n1, v1, next1) &*&
                result == (v0 < v1 ? -1 : (v0 > v1 ? 1 : 0)); @*/
{
  // VeriFast automatically opens the list_node predicates to access the fields.
  if (n0->value < n1->value) {
    return -1;
  } else if (n0->value > n1->value) {
    return 1;
  } else {
    return 0;
  }
  // VeriFast automatically closes the predicates before returning,
  // verifying that the nodes were not modified.
}