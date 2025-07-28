// Definition of a singly linked list node holding an integer value
struct list_node {
  int value;
  struct list_node* next;
};


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
{
  if (*pfirst == 0) {
    return;
  }  
  
  struct list_node* last_sorted = *pfirst;
  while (last_sorted->next != 0)
  {
    
    struct list_node** pn = pfirst;
    int comparison = compare(*pn, last_sorted->next);
    while (pn != &(last_sorted->next) && comparison < 0)
    { 
      pn = &((*pn)->next);
      
      
      if (pn != &(last_sorted->next)) {

        comparison = compare(*pn, last_sorted->next);
      } else {
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

}


// TODO: make this function pass the verification
/***
 * Description:
The insertion_sort function is a wrapper function that initiates sorting on a given linked list.

@param l - pointer to the head of the list.
@return pointer to the head of the list.

It makes sure that after the sort, the retrun value still points to the head of a list.
*/
struct list_node* insertion_sort(struct list_node* l)
{
  insertion_sort_core(&l);
  return l;
}

