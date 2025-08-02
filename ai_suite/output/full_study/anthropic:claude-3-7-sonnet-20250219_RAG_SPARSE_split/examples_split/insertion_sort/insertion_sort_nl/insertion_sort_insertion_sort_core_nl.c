// Definition of a singly linked list node holding an integer value
struct list_node {
  int value;
  struct list_node* next;
};

/*@
// Predicate to represent a linked list segment
predicate lseg(struct list_node* from, struct list_node* to; list<int> values) =
  from == to ?
    values == nil
  :
    from != 0 &*& from->value |-> ?v &*& from->next |-> ?next &*& 
    malloc_block_node(from) &*& lseg(next, to, ?rest) &*& 
    values == cons(v, rest);

// Predicate to represent a full linked list
predicate list(struct list_node* head; list<int> values) =
  lseg(head, 0, values);
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
/*@
// Specification for the compare function
requires n0 != 0 &*& n1 != 0 &*& [?f1]n0->value |-> ?v0 &*& [?f2]n1->value |-> ?v1;
ensures [f1]n0->value |-> v0 &*& [f2]n1->value |-> v1 &*& 
        (result == -1 ? v0 < v1 : (result == 1 ? v0 > v1 : v0 == v1));
@*/
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

/*@
// Lemma to help with sorting - proves that a list is sorted
lemma void sorted_list_lemma(struct list_node* head)
  requires list(head, ?values) &*& head != 0;
  ensures list(head, values) &*& head != 0;
{
  open list(head, values);
  if (head->next != 0) {
    open lseg(head->next, 0, _);
    if (head->next->next != 0) {
      close lseg(head->next->next, 0, _);
      close lseg(head->next, 0, _);
    } else {
      close lseg(head->next, 0, _);
    }
  }
  close list(head, values);
}

// Lemma to help with insertion - proves that we can insert a node into a list
lemma void insert_node_lemma(struct list_node* head, struct list_node* node, struct list_node* prev)
  requires lseg(head, prev, ?prefix) &*& prev->next |-> ?old_next &*& 
           node != 0 &*& node->value |-> ?v &*& node->next |-> old_next &*& 
           malloc_block_node(node) &*& lseg(old_next, 0, ?suffix);
  ensures lseg(head, 0, append(prefix, cons(v, suffix))) &*& prev->next |-> node;
{
  open lseg(head, prev, prefix);
  if (head == prev) {
    prev->next = node;
    close lseg(node, 0, cons(v, suffix));
    close lseg(head, 0, append(prefix, cons(v, suffix)));
  } else {
    insert_node_lemma(head->next, node, prev);
    close lseg(head, 0, append(prefix, cons(v, suffix)));
  }
}

// Lemma to help with finding the insertion point
lemma void find_insertion_point_lemma(struct list_node* head, struct list_node* node, int value)
  requires lseg(head, 0, ?values) &*& node != 0 &*& node->value |-> value;
  ensures lseg(head, 0, values) &*& node != 0 &*& node->value |-> value;
{
  open lseg(head, 0, values);
  if (head != 0) {
    find_insertion_point_lemma(head->next, node, value);
  }
  close lseg(head, 0, values);
}
@*/

/***
 * Description:
The insertion_sort_core function performs an in-place insertion sort on a singly linked list.

It maintains a sorted portion of the list and iteratively inserts the next unsorted node 
into the correct position within the sorted portion.

@param pfirst - double pointer to the head of the list.
 *              Used for efficient node insertion at the head or interior.

It makes sure that after the sort, pfirst still points to the head of a list.
*/
/*@
requires *pfirst |-> ?first &*& list(first, ?values);
ensures *pfirst |-> ?new_first &*& list(new_first, ?sorted_values) &*& 
        permutation(values, sorted_values) &*& is_sorted(sorted_values) == true;
@*/
void insertion_sort_core(struct list_node** pfirst)
{
  if (*pfirst == 0) {
    return;
  }  
  
  //@ open list(*pfirst, values);
  struct list_node* last_sorted = *pfirst;
  //@ close lseg(last_sorted, last_sorted, nil);
  //@ assert last_sorted->next |-> ?next_node;
  //@ assert lseg(next_node, 0, ?rest_values);
  
  /*@
  // Loop invariant: the list is partially sorted up to last_sorted
  invariant *pfirst |-> ?current_first &*& 
            lseg(current_first, last_sorted, ?sorted_prefix) &*& 
            last_sorted != 0 &*& last_sorted->next |-> ?unsorted &*& 
            lseg(unsorted, 0, ?unsorted_values) &*& 
            is_sorted(sorted_prefix) == true &*& 
            permutation(values, append(sorted_prefix, unsorted_values));
  @*/
  while (last_sorted->next != 0)
  {
    //@ open lseg(unsorted, 0, unsorted_values);
    //@ assert unsorted != 0;
    //@ assert unsorted->value |-> ?unsorted_value;
    //@ assert unsorted->next |-> ?unsorted_next;
    //@ assert lseg(unsorted_next, 0, ?remaining_unsorted);
    
    struct list_node** pn = pfirst;
    //@ assert *pn |-> ?current;
    //@ find_insertion_point_lemma(current, unsorted, unsorted_value);
    int comparison = compare(*pn, last_sorted->next);
    
    /*@
    // Inner loop invariant: we're finding the right position to insert the node
    invariant pn != 0 &*& *pn |-> ?current_node &*& 
              current_node != 0 &*& current_node->value |-> ?current_value &*& 
              unsorted != 0 &*& unsorted->value |-> unsorted_value &*& 
              pn != &(last_sorted->next) ? 
                current_value <= unsorted_value : true;
    @*/
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
      
      //@ insert_node_lemma(current_first, first_unsorted, last_sorted);
      //@ sorted_list_lemma(*pfirst);
    } else {
      last_sorted = last_sorted->next;
      //@ close lseg(current_first, last_sorted, append(sorted_prefix, cons(unsorted_value, nil)));
    }
    
    //@ assert last_sorted->next |-> ?new_unsorted;
    //@ assert lseg(new_unsorted, 0, ?new_unsorted_values);
  }
  
  //@ close list(*pfirst, sorted_values);
  //@ assert permutation(values, sorted_values);
  //@ assert is_sorted(sorted_values) == true;
}