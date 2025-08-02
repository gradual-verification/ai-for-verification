// Definition of a singly linked list node holding an integer value
struct list_node {
  int value;
  struct list_node* next;
};

/*@
// Define a predicate for a linked list segment
predicate lseg(struct list_node* from, struct list_node* to, list<int> values) =
  from == to ?
    values == nil
  :
    from != 0 &*& from->value |-> ?v &*& from->next |-> ?next &*& 
    malloc_block_node(from) &*& lseg(next, to, ?tail) &*& 
    values == cons(v, tail);

// Define a predicate for a complete linked list
predicate list(struct list_node* head, list<int> values) =
  lseg(head, 0, values);

// Lemma to help with comparing nodes
lemma void compare_values_preserved(struct list_node* n0, struct list_node* n1)
  requires n0->value |-> ?v0 &*& n1->value |-> ?v1;
  ensures n0->value |-> v0 &*& n1->value |-> v1;
{
}

// Lemma to help with insertion sort
lemma void lseg_split(struct list_node* from, struct list_node* split)
  requires lseg(from, 0, ?values) &*& split != 0;
  ensures lseg(from, split, ?prefix) &*& lseg(split, 0, ?suffix) &*& values == append(prefix, suffix);
{
  open lseg(from, 0, values);
  if (from == split) {
    close lseg(from, from, nil);
  } else {
    lseg_split(from->next, split);
    close lseg(from, split, _);
  }
}

// Lemma to help with insertion sort
lemma void lseg_join(struct list_node* from, struct list_node* mid)
  requires lseg(from, mid, ?prefix) &*& lseg(mid, 0, ?suffix);
  ensures lseg(from, 0, append(prefix, suffix));
{
  open lseg(from, mid, prefix);
  if (from == mid) {
    // Base case
  } else {
    lseg_join(from->next, mid);
    close lseg(from, 0, append(prefix, suffix));
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
//@ requires n0 != 0 &*& n1 != 0 &*& n0->value |-> ?v0 &*& n1->value |-> ?v1;
//@ ensures n0->value |-> v0 &*& n1->value |-> v1 &*& (result == -1 ? v0 < v1 : (result == 1 ? v0 > v1 : v0 == v1));
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
//@ requires *pfirst |-> ?first &*& list(first, ?values);
//@ ensures *pfirst |-> ?sorted &*& list(sorted, ?sorted_values) &*& permutation(values, sorted_values) &*& sorted_list(sorted_values);
{
  if (*pfirst == 0) {
    //@ close sorted_list(nil);
    return;
  }  
  
  struct list_node* last_sorted = *pfirst;
  //@ open list(first, values);
  //@ assert last_sorted->next |-> ?next_node;
  //@ assert lseg(next_node, 0, ?rest_values);
  //@ close lseg(last_sorted, last_sorted, nil);
  //@ assert last_sorted->value |-> ?first_value;
  //@ close sorted_list(cons(first_value, nil));
  
  while (last_sorted->next != 0)
  //@ invariant last_sorted != 0 &*& *pfirst |-> ?current &*& lseg(current, last_sorted, ?sorted_prefix) &*& 
  //@ last_sorted->next |-> ?next_unsorted &*& last_sorted->value |-> ?last_value &*& 
  //@ malloc_block_node(last_sorted) &*& lseg(next_unsorted, 0, ?unsorted_suffix) &*& 
  //@ values == append(append(sorted_prefix, cons(last_value, nil)), unsorted_suffix) &*&
  //@ sorted_list(append(sorted_prefix, cons(last_value, nil)));
  {
    //@ open lseg(next_unsorted, 0, unsorted_suffix);
    //@ assert next_unsorted->value |-> ?first_unsorted_value;
    //@ assert next_unsorted->next |-> ?rest_unsorted;
    
    struct list_node** pn = pfirst;
    //@ assert *pn |-> current;
    int comparison = compare(*pn, last_sorted->next);
    //@ assert (*pn)->value |-> ?current_value;
    
    while (pn != &(last_sorted->next) && comparison < 0)
    //@ invariant pn != 0 &*& *pn |-> ?current_node &*& current_node != 0 &*& 
    //@ lseg(*pfirst, current_node, ?prefix) &*& current_node->value |-> ?node_value &*& 
    //@ current_node->next |-> ?node_next &*& malloc_block_node(current_node) &*& 
    //@ lseg(node_next, last_sorted->next, ?middle) &*& 
    //@ append(append(prefix, cons(node_value, middle)), cons(first_unsorted_value, nil)) == append(sorted_prefix, cons(last_value, nil));
    { 
      pn = &((*pn)->next);
      //@ assert *pn |-> ?new_current;
      
      if (pn != &(last_sorted->next)) {
        comparison = compare(*pn, last_sorted->next);
        //@ assert (*pn)->value |-> ?new_value;
      } else {
      }
    }
    
    if (pn != &(last_sorted->next)) {
      struct list_node* first_unsorted = last_sorted->next;
      last_sorted->next = first_unsorted->next;
      first_unsorted->next = *pn;
      *pn = first_unsorted;     
      //@ sorted_list_insert(append(sorted_prefix, cons(last_value, nil)), first_unsorted_value);
    } else {
      last_sorted = last_sorted->next;
      //@ sorted_list_append(append(sorted_prefix, cons(last_value, nil)), first_unsorted_value);
    }
  }
  //@ open lseg(next_unsorted, 0, unsorted_suffix);
  //@ assert unsorted_suffix == nil;
  //@ close list(*pfirst, append(sorted_prefix, cons(last_value, nil)));
}

/*@
// Define a predicate for a sorted list
predicate sorted_list(list<int> values) =
  switch(values) {
    case nil: return true;
    case cons(h, t): 
      return switch(t) {
        case nil: return true;
        case cons(h2, t2): return h <= h2 &*& sorted_list(t);
      };
  };

// Lemma to prove that inserting a value into a sorted list maintains sortedness
lemma void sorted_list_insert(list<int> sorted_values, int value)
  requires sorted_list(sorted_values);
  ensures sorted_list(insert_sorted(sorted_values, value));
{
  switch(sorted_values) {
    case nil:
      close sorted_list(cons(value, nil));
    case cons(h, t):
      if (value <= h) {
        close sorted_list(cons(value, sorted_values));
      } else {
        sorted_list_insert(t, value);
        close sorted_list(cons(h, insert_sorted(t, value)));
      }
  }
}

// Lemma to prove that appending a value to a sorted list maintains sortedness if the value is greater than the last element
lemma void sorted_list_append(list<int> sorted_values, int value)
  requires sorted_list(sorted_values) &*& (sorted_values == nil || last(sorted_values) <= value);
  ensures sorted_list(append(sorted_values, cons(value, nil)));
{
  switch(sorted_values) {
    case nil:
      close sorted_list(cons(value, nil));
    case cons(h, t):
      sorted_list_append(t, value);
      close sorted_list(cons(h, append(t, cons(value, nil))));
  }
}

// Helper function to get the last element of a list
fixpoint int last(list<int> values) {
  switch(values) {
    case nil: return 0; // Should not happen
    case cons(h, t): return t == nil ? h : last(t);
  }
}

// Helper function to insert a value into a sorted list
fixpoint list<int> insert_sorted(list<int> sorted_values, int value) {
  switch(sorted_values) {
    case nil: return cons(value, nil);
    case cons(h, t): return value <= h ? cons(value, sorted_values) : cons(h, insert_sorted(t, value));
  }
}

// Define a predicate for permutation of lists
predicate permutation(list<int> l1, list<int> l2) =
  length(l1) == length(l2) &*& 
  forall_int(i => 0 <= i && i < length(l1) ? count(l1, nth(l1, i)) == count(l2, nth(l1, i)) : true);

// Helper function to count occurrences of a value in a list
fixpoint int count(list<int> values, int value) {
  switch(values) {
    case nil: return 0;
    case cons(h, t): return (h == value ? 1 : 0) + count(t, value);
  }
}
@*/

// TODO: make this function pass the verification
/***
 * Description:
The insertion_sort function is a wrapper function that initiates sorting on a given linked list.

@param l - pointer to the head of the list.
@return pointer to the head of the list.

It makes sure that after the sort, the retrun value still points to the head of a list.
*/
struct list_node* insertion_sort(struct list_node* l)
//@ requires list(l, ?values);
//@ ensures list(result, ?sorted_values) &*& permutation(values, sorted_values) &*& sorted_list(sorted_values);
{
  //@ close l |-> l;
  insertion_sort_core(&l);
  //@ open l |-> _;
  return l;
}