struct list_node {
  int value;
  struct list_node* next;
};

/*@
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

/*@
// Helper lemma to extract a node from a list
lemma void extract_node(struct list_node* head, struct list_node* target)
  requires list_pred(head) &*& head != 0 &*& target != 0;
  ensures head->value |-> ?v &*& head->next |-> ?next &*& 
          (head == target ? true : list_pred(next));
{
  open list_pred(head);
  if (head != target) {
    if (head->next != 0) {
      extract_node(head->next, target);
    }
  }
}

// Helper lemma to close a list after extracting a node
lemma void close_list_after_extract(struct list_node* head, struct list_node* target)
  requires head->value |-> ?v &*& head->next |-> ?next &*& 
           (head == target ? true : list_pred(next));
  ensures list_pred(head);
{
  if (head != target) {
    close list_pred(head);
  } else {
    close list_pred(head);
  }
}

// Helper lemma to extract a node and its predecessor
lemma void extract_node_and_prev(struct list_node* head, struct list_node* target)
  requires list_pred(head) &*& head != 0 &*& target != 0 &*& head != target;
  ensures head->value |-> ?v &*& head->next |-> ?next &*& 
          (next == target ? 
            target->value |-> ?tv &*& target->next |-> ?tnext &*& list_pred(tnext) : 
            list_pred(next));
{
  open list_pred(head);
  if (head->next != target) {
    if (head->next != 0) {
      extract_node_and_prev(head->next, target);
    }
  } else {
    open list_pred(target);
  }
}

// Helper lemma to close a list after extracting a node and its predecessor
lemma void close_list_after_extract_and_prev(struct list_node* head, struct list_node* target, struct list_node* new_next)
  requires head->value |-> ?v &*& head->next |-> ?next &*& 
           (next == target ? 
             target->value |-> ?tv &*& target->next |-> new_next &*& list_pred(new_next) : 
             list_pred(next));
  ensures list_pred(head);
{
  if (head->next == target) {
    close list_pred(target);
  }
  close list_pred(head);
}
@*/

void insertion_sort_core(struct list_node** pfirst)
//@ requires *pfirst |-> ?l &*& list_pred(l);
//@ ensures *pfirst |-> ?l0 &*& list_pred(l0);
{
  if (*pfirst == 0) {
    return;
  }  
  
  struct list_node* last_sorted = *pfirst;
  //@ open list_pred(l);
  //@ close list_pred(l);
  
  while (last_sorted->next != 0)
  //@ invariant *pfirst |-> ?current &*& current != 0 &*& list_pred(current) &*& last_sorted != 0;
  {
    //@ extract_node(current, last_sorted);
    //@ extract_node(last_sorted, last_sorted->next);
    
    struct list_node** pn = pfirst;
    int comparison = compare(*pn, last_sorted->next);
    
    while (pn != &(last_sorted->next) && comparison < 0)
    //@ invariant *pn |-> ?node &*& node != 0 &*& pn != 0 &*& list_pred(current);
    { 
      pn = &((*pn)->next);
      
      if (pn != &(last_sorted->next)) {
        //@ extract_node(current, *pn);
        comparison = compare(*pn, last_sorted->next);
        //@ close_list_after_extract(current, *pn);
      } else {
        // No need to compare if we've reached last_sorted->next
      }
    }
    
    if (pn != &(last_sorted->next)) {
      // Need to move the first unsorted element to its sorted position
      struct list_node* first_unsorted = last_sorted->next;
      //@ extract_node(first_unsorted, first_unsorted);
      
      last_sorted->next = first_unsorted->next;
      //@ close list_pred(first_unsorted->next);
      //@ close list_pred(last_sorted);
      
      //@ extract_node(current, *pn);
      first_unsorted->next = *pn;
      *pn = first_unsorted;
      //@ close list_pred(first_unsorted);
      //@ close list_pred(current);
    } else {
      // The first unsorted element is already in the right position
      last_sorted = last_sorted->next;
      //@ close list_pred(last_sorted);
      //@ close list_pred(current);
    }
  }
}