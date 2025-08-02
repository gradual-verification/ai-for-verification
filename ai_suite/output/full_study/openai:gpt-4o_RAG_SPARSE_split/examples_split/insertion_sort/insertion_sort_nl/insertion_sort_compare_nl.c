#include "stdlib.h"

// Definition of a singly linked list node holding an integer value
struct list_node {
  int value;
  struct list_node* next;
};

//@ predicate list_node(struct list_node* node, int value, struct list_node* next) =
//@   node->value |-> value &*& node->next |-> next &*& malloc_block_list_node(node);

//@ predicate list(struct list_node* head, list<int> values) =
//@   head == 0 ? values == nil : list_node(head, ?value, ?next) &*& list(next, ?values_tail) &*& values == cons(value, values_tail);

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
//@ requires list_node(n0, ?v0, ?next0) &*& list_node(n1, ?v1, ?next1);
//@ ensures list_node(n0, v0, next0) &*& list_node(n1, v1, next1) &*& (result == -1 ? v0 < v1 : result == 1 ? v0 > v1 : v0 == v1);
static int compare(struct list_node* n0, struct list_node* n1)
{
  //@ open list_node(n0, ?v0, ?next0);
  //@ open list_node(n1, ?v1, ?next1);
  if (n0->value < n1->value) {
    //@ close list_node(n0, v0, next0);
    //@ close list_node(n1, v1, next1);
    return -1;
  } else if (n0->value > n1->value) {
    //@ close list_node(n0, v0, next0);
    //@ close list_node(n1, v1, next1);
    return 1;
  } else {
    //@ close list_node(n0, v0, next0);
    //@ close list_node(n1, v1, next1);
    return 0;
  }
}