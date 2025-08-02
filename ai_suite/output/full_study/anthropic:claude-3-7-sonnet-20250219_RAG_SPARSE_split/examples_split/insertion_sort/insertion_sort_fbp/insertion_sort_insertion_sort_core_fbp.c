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
// Helper lemma to split a list at a specific node
lemma void list_pred_split(struct list_node* head, struct list_node* target)
  requires list_pred(head) &*& target != 0;
  ensures list_pred(head) &*& target->value |-> ?v &*& target->next |-> ?n;
{
  if (head == 0) {
    return;
  }
  open list_pred(head);
  if (head == target) {
    close list_pred(head->next);
  } else {
    list_pred_split(head->next, target);
  }
  close list_pred(head);
}

// Helper lemma to join a split list
lemma void list_pred_join(struct list_node* head, struct list_node* target)
  requires list_pred(head) &*& target->value |-> ?v &*& target->next |-> ?n &*& list_pred(n);
  ensures list_pred(head);
{
  if (head == 0) {
    return;
  }
  open list_pred(head);
  if (head == target) {
    close list_pred(head);
  } else {
    list_pred_join(head->next, target);
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
  //@ close list_pred(last_sorted->next);
  
  while (last_sorted->next != 0)
  //@ invariant *pfirst |-> ?current &*& last_sorted->next |-> ?next_node &*& list_pred(next_node) &*& last_sorted != 0;
  {
    //@ list_pred_split(current, last_sorted);
    
    struct list_node** pn = pfirst;
    //@ assert *pn |-> ?first;
    //@ assert list_pred(first);
    //@ list_pred_split(first, last_sorted->next);
    
    int comparison = compare(*pn, last_sorted->next);
    
    while (pn != &(last_sorted->next) && comparison < 0)
    //@ invariant pn != 0 &*& *pn |-> ?node &*& list_pred(node) &*& last_sorted->next |-> ?unsorted &*& unsorted != 0 &*& unsorted->value |-> ?uval &*& unsorted->next |-> ?unext &*& list_pred(unext);
    { 
      pn = &((*pn)->next);
      //@ open list_pred(node);
      //@ close list_pred(node);
      
      if (pn != &(last_sorted->next)) {
        //@ list_pred_split(*pn, last_sorted->next);
        comparison = compare(*pn, last_sorted->next);
      } else {
        //@ list_pred_join(first, last_sorted->next);
      }
    }
    
    if (pn != &(last_sorted->next)) {
      struct list_node* first_unsorted = last_sorted->next;
      last_sorted->next = first_unsorted->next;
      //@ open list_pred(first_unsorted);
      first_unsorted->next = *pn;
      *pn = first_unsorted;
      //@ close list_pred(first_unsorted);
      //@ list_pred_join(first, first_unsorted);
    } else {
      last_sorted = last_sorted->next;
      //@ list_pred_join(first, last_sorted);
    }
    
    //@ list_pred_join(current, last_sorted);
  }
  
  //@ close list_pred(l0);
}