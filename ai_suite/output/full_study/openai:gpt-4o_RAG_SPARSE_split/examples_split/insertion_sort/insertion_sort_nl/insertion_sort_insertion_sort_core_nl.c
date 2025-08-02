#include "stdlib.h"
#include "prelude.h"

// Definition of a singly linked list node holding an integer value
struct list_node {
  int value;
  struct list_node* next;
};

/*@
predicate list(struct list_node* node, list<int> values) =
  node == 0 ? 
    values == nil 
  : 
    node->value |-> ?v &*& node->next |-> ?n &*& malloc_block_list_node(node) &*& list(n, ?vs) &*& values == cons(v, vs);

fixpoint bool sorted(list<int> values) {
  switch (values) {
    case nil: return true;
    case cons(x, nil): return true;
    case cons(x, cons(y, ys)): return x <= y && sorted(cons(y, ys));
  }
}
@*/

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
  //@ requires n0->value |-> ?v0 &*& n1->value |-> ?v1;
  //@ ensures n0->value |-> v0 &*& n1->value |-> v1 &*& (result == -1 ? v0 < v1 : result == 1 ? v0 > v1 : v0 == v1);
{
  if (n0->value < n1->value) {
    return -1;
  } else if (n0->value > n1->value) {
    return 1;
  } else {
    return 0;
  }
}

// TODO: make this function pass the verification
/***
 * Description:
The insertion_sort_core function performs an in-place insertion sort on a singly linked list.

It maintains a sorted portion of the list and iteratively inserts the next unsorted node 
into the correct position within the sorted portion.

@param pfirst - double pointer to the head of the list.
 *              Used for efficient node insertion at the head or interior.

It makes sure that after the sort, pfirst still points to the head of a list.
*/
void insertion_sort_core(struct list_node** pfirst)
  //@ requires pointer(pfirst, ?first) &*& list(first, ?values);
  //@ ensures pointer(pfirst, ?new_first) &*& list(new_first, ?sorted_values) &*& sorted(sorted_values) == true;
{
  if (*pfirst == 0) {
    return;
  }  
  
  struct list_node* last_sorted = *pfirst;
  //@ open list(last_sorted, _);
  while (last_sorted->next != 0)
    //@ invariant list(*pfirst, ?sorted_values) &*& sorted(sorted_values) == true &*& list(last_sorted->next, ?unsorted_values);
  {
    struct list_node** pn = pfirst;
    int comparison = compare(*pn, last_sorted->next);
    while (pn != &(last_sorted->next) && comparison < 0)
      //@ invariant list(*pfirst, ?sorted_values) &*& sorted(sorted_values) == true &*& list(last_sorted->next, ?unsorted_values) &*& list(*pn, ?current_values);
    { 
      pn = &((*pn)->next);
      if (pn != &(last_sorted->next)) {
        comparison = compare(*pn, last_sorted->next);
      }
    }
    
    if (pn != &(last_sorted->next)) {
      struct list_node* first_unsorted = last_sorted->next;
      last_sorted->next = first_unsorted->next;
      first_unsorted->next = *pn;
      *pn = first_unsorted;
    } else {
      last_sorted = last_sorted->next;
    }
  }
  //@ close list(*pfirst, _);
}