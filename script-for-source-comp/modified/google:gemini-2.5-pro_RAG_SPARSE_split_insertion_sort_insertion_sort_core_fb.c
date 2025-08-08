
struct list_node {
  int value;
  struct list_node* next;
};



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


void insertion_sort_core(struct list_node** pfirst)
{
  if (*pfirst == 0) {
    return;
  }  
  
  struct list_node* last_sorted = *pfirst;
  while (last_sorted->next != 0)
  {
    struct list_node* node_to_insert = last_sorted->next;
    
    struct list_node** pn = pfirst;
    
    
    int comparison = compare(*pn, node_to_insert);
    
    while (pn != &(last_sorted->next) && comparison < 0)
    {
      pn = &((*pn)->next);
      
      if (pn != &(last_sorted->next)) {
        comparison = compare(*pn, node_to_insert);
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
