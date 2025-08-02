#include "stdlib.h"
#include "prelude.h"

// Definition of a singly linked list node holding an integer value
struct list_node {
  int value;
  struct list_node* next;
};

/*@
predicate lseg(struct list_node* from, struct list_node* to, list<int> values) =
  from == to ? values == nil : from->value |-> ?v &*& from->next |-> ?n &*& malloc_block_list_node(from) &*& lseg(n, to, ?vs) &*& values == cons(v, vs);

predicate list(struct list_node* n, list<int> values) = lseg(n, 0, values);

fixpoint bool sorted(list<int> xs) {
  switch (xs) {
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
  //@ ensures pointer(pfirst, ?new_first) &*& list(new_first, ?sorted_values) &*& sorted(sorted_values);
{
  if (*pfirst == 0) {
    return;
  }  
  
  struct list_node* last_sorted = *pfirst;
  //@ open list(last_sorted, values);
  while (last_sorted->next != 0)
  //@ invariant lseg(*pfirst, last_sorted->next, ?sorted_part) &*& sorted(sorted_part) &*& lseg(last_sorted->next, 0, ?unsorted_part);
  {
    struct list_node** pn = pfirst;
    int comparison = compare(*pn, last_sorted->next);
    while (pn != &(last_sorted->next) && comparison < 0)
    //@ invariant lseg(*pfirst, *pn, ?sorted_prefix) &*& lseg(*pn, last_sorted->next, ?sorted_suffix) &*& sorted(append(sorted_prefix, sorted_suffix)) &*& lseg(last_sorted->next, 0, ?unsorted_part);
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
  //@ close list(*pfirst, append(sorted_part, unsorted_part));
}

/***
 * Description:
The insertion_sort function is a wrapper function that initiates sorting on a given linked list.

@param l - pointer to the head of the list.
@return pointer to the head of the list.

It makes sure that after the sort, the return value still points to the head of a list.
*/
struct list_node* insertion_sort(struct list_node* l)
  //@ requires list(l, ?values);
  //@ ensures list(result, ?sorted_values) &*& sorted(sorted_values);
{
  insertion_sort_core(&l);
  return l;
}