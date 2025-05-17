/**
 * This example consists of an insertion sort algorithm for linked lists of integers,
 * verified for memory safety.
 *
 * @date 13 Aug 2014
 * @author Pieter Agten <pieter.agten@cs.kuleuven.be>
 */


struct list_node {
  int value;
  struct list_node* next;
};

/*@
  // Predicate describing a complete linked list
  predicate list_pred(struct list_node* n;) =
    n == 0 ? 
      true
    :
      n->value |-> ?nValue &*& n->next |-> ?next &*& list_pred(next);
@*/

static int compare(struct list_node* n0, struct list_node* n1)
//@ requires n0->value |-> ?v0 &*& n1->value |-> ?v1;
//@ ensures n0->value |-> v0 &*& n1->value |-> v1 &*& result == (v0 < v1 ? -1 : v0 > v1 ? 1 : 0);
{
  if (n0->value < n1->value) {
    return -1;
  } else if (n0->value > n1->value) {
    return 1;
  } else {
    return 0;
  }
}

void insertion_sort_core(struct list_node** pfirst)
//@ requires *pfirst |-> ?l &*& list_pred(l);
//@ ensures *pfirst |-> ?l0 &*& list_pred(l0);
{
  if (*pfirst == 0) {
    // Empty list is trivially sorted
    return;
  }  
  
  struct list_node* last_sorted = *pfirst;
  while (last_sorted->next != 0)
  {
    
    struct list_node** pn = pfirst;
    int comparison = compare(*pn, last_sorted->next); // Cannot inline this call into the while-condition, because of C's unspecified evaluation order in this case
    while (pn != &(last_sorted->next) && comparison < 0)
    { 
      pn = &((*pn)->next);
      
      
      if (pn != &(last_sorted->next)) {

        comparison = compare(*pn, last_sorted->next);
      } else {
      }
    }
    
    
    // Found insertion point (right before *pn), so let's move the first unsorted
    // node into the sorted part, right before *pn.
    if (pn != &(last_sorted->next)) {
      struct list_node* first_unsorted = last_sorted->next;
      // Remove first unsorted element from list
      last_sorted->next = first_unsorted->next;
      // Insert first unsorted element at right position in list
      first_unsorted->next = *pn;
      *pn = first_unsorted;     
    } else {
      // First unsorted element is already in the correct position
      last_sorted = last_sorted->next;
    }
  }

}


struct list_node* insertion_sort(struct list_node* l)
//@ requires list_pred(l);
//@ ensures list_pred(result);
{
  insertion_sort_core(&l);
  return l;
}

