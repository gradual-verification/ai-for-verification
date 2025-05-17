/**
 * This example consists of an insertion sort algorithm for linked lists of integers,
 * verified for memory safety.
 *
 * @date 13 Aug 2014
 * @author Pieter Agten <pieter.agten@cs.kuleuven.be>
 */

// Definition of a singly linked list node holding an integer value
struct list_node {
  int value;
  struct list_node* next;
};

/***
 * Function: compare
 *
 * Description:
 * Compares the integer values of two linked list nodes.
 *
@param n0 - pointer to the first node.
@param n1 - pointer to the second node.
@return -1 if n0's value < n1's value,
 *          1 if n0's value > n1's value,
 *          0 if equal.
 */
static int compare(struct list_node* n0, struct list_node* n1)
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
 * Function: insertion_sort_core
 *
 * Description:
 * Performs an in-place insertion sort on a singly linked list.
 * The algorithm maintains a sorted portion of the list and iteratively
 * inserts the next unsorted node into the correct position within the sorted portion.
 *
@param pfirst - double pointer to the head of the list.
 *                 Used for efficient node insertion at the head or interior.
 */
void insertion_sort_core(struct list_node** pfirst)
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

/***
 * Function: insertion_sort
 *
 * Description:
 * Wrapper function that initiates sorting on a given linked list.
 *
@param l - pointer to the head of the list.
@return pointer to the head of the sorted list.
 */
struct list_node* insertion_sort(struct list_node* l)
{
  insertion_sort_core(&l);
  return l;
}

