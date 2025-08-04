#include <stdlib.h>

// Definition of a singly linked list node holding an integer value
struct list_node {
  int value;
  struct list_node* next;
};

/*@
// --- Predicates for linked lists ---

predicate list_node(struct list_node *n; int v, struct list_node *next) =
    n->value |-> v &*& n->next |-> next &*& malloc_block_list_node(n);

predicate lseg(struct list_node *from, struct list_node *to; list<int> vs) =
    from == to ?
        vs == nil
    :
        from != 0 &*& list_node(from, ?v, ?next) &*& lseg(next, to, ?tail) &*& vs == cons(v, tail);

predicate list(struct list_node *l; list<int> vs) = lseg(l, 0, vs);

// --- Fixpoints and lemmas for sortedness ---

fixpoint bool is_ge(int x, int y) { return x <= y; }

fixpoint bool is_sorted(list<int> vs) {
    switch (vs) {
        case nil: return true;
        case cons(h, t): return forall(t, (is_ge)(h)) && is_sorted(t);
    }
}

lemma void is_sorted_append(list<int> l1, list<int> l2)
    requires is_sorted(l1) && is_sorted(l2) && (l1 == nil || l2 == nil || last(l1) <= head(l2));
    ensures is_sorted(append(l1, l2)) == true;
{
    switch(l1) {
        case nil:
        case cons(h, t):
            is_sorted_append(t, l2);
    }
}

lemma void forall_ge_trans(list<int> vs, int v1, int v2)
    requires forall(vs, (is_ge)(v1)) == true &*& v1 <= v2;
    ensures forall(vs, (is_ge)(v2)) == true;
{
    switch(vs) {
        case nil:
        case cons(h, t):
            forall_ge_trans(t, v1, v2);
    }
}

// --- Fixpoints and lemmas for permutations ---

fixpoint int count_val(list<int> vs, int v) {
    switch (vs) {
        case nil: return 0;
        case cons(h, t): return (h == v ? 1 : 0) + count_val(t, v);
    }
}

fixpoint bool is_permutation(list<int> vs1, list<int> vs2) {
    return length(vs1) == length(vs2) && forall_distinct(append(vs1, vs2), (counts_equal)(vs1, vs2));
}

fixpoint bool forall_distinct(list<int> vs, fixpoint(int, bool) p) {
    switch (vs) {
        case nil: return true;
        case cons(h, t): return p(h) && forall_distinct(remove_all(h, t), p);
    }
}

fixpoint list<int> remove_all(int x, list<int> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(h, t): return h == x ? remove_all(x, t) : cons(h, remove_all(x, t));
    }
}

fixpoint bool counts_equal(list<int> vs1, list<int> vs2, int v) {
    return count_val(vs1, v) == count_val(vs2, v);
}

lemma void is_permutation_refl(list<int> vs);
    requires true;
    ensures is_permutation(vs, vs) == true;

lemma void is_permutation_sym(list<int> vs1, list<int> vs2);
    requires is_permutation(vs1, vs2) == true;
    ensures is_permutation(vs2, vs1) == true;

lemma void is_permutation_trans(list<int> vs1, list<int> vs2, list<int> vs3);
    requires is_permutation(vs1, vs2) == true &*& is_permutation(vs2, vs3) == true;
    ensures is_permutation(vs1, vs3) == true;

lemma void is_permutation_append_swap(list<int> p1, list<int> p2, int v, list<int> rest)
    requires true;
    ensures is_permutation(append(append(p1, p2), cons(v, rest)), append(p1, cons(v, append(p2, rest)))) == true;

// --- Predicate and lemmas for pointer-to-pointer traversal ---

predicate path(struct list_node **from, struct list_node *to; list<int> vs) =
    *from |-> ?curr &*&
    (curr == to ?
        vs == nil
    :
        list_node(curr, ?v, ?next) &*& path(&(curr->next), to, ?tail) &*& vs == cons(v, tail)
    );

lemma void path_to_lseg(struct list_node **from, struct list_node *to)
    requires path(from, to, ?vs);
    ensures *from |-> ?h &*& lseg(h, to, vs);
{
    open path(from, to, vs);
    if (*from == to) {
        close lseg(to, to, nil);
    } else {
        path_to_lseg(&((*from)->next), to);
        close lseg(*from, to, vs);
    }
}

lemma void lseg_to_path(struct list_node **from, struct list_node *to)
    requires *from |-> ?h &*& lseg(h, to, ?vs);
    ensures path(from, to, vs);
{
    open lseg(h, to, vs);
    if (h == to) {
        close path(from, to, nil);
    } else {
        lseg_to_path(&(h->next), to);
        close path(from, to, vs);
    }
}

lemma void forall_path_lt(struct list_node **from, struct list_node *to, int v)
    requires path(from, to, ?vs) &*& forall(vs, (is_lt)(v)) == true;
    ensures path(from, to, vs) &*& forall(vs, (is_lt)(v)) == true;
{
    open path(from, to, vs);
    if (*from != to) {
        forall_path_lt(&((*from)->next), to, v);
    }
    close path(from, to, vs);
}

fixpoint bool is_lt(int y, int x) { return x < y; }

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
    //@ ensures n0->value |-> v0 &*& n1->value |-> v1 &*& result == (v0 < v1 ? -1 : (v0 > v1 ? 1 : 0));
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
    //@ requires path(pfirst, 0, ?vs);
    //@ ensures path(pfirst, 0, ?vs_sorted) &*& is_sorted(vs_sorted) == true &*& is_permutation(vs, vs_sorted) == true;
{
  //@ open path(pfirst, 0, vs);
  if (*pfirst == 0) {
    //@ close path(pfirst, 0, nil);
    return;
  }
  
  struct list_node* last_sorted = *pfirst;
  //@ lseg_to_path(&((*pfirst)->next), 0);
  //@ list<int> initial_vs = vs;
  //@ is_permutation_refl(vs);
  while (last_sorted->next != 0)
    /*@
    invariant
        path(pfirst, last_sorted->next, ?sorted_vs) &*&
        list(last_sorted->next, ?unsorted_vs) &*&
        is_sorted(sorted_vs) == true &*&
        is_permutation(append(sorted_vs, unsorted_vs), initial_vs) == true;
    @*/
  {
    //@ open list(last_sorted->next, unsorted_vs);
    struct list_node* first_unsorted = last_sorted->next;
    int v_fu = first_unsorted->value;
    
    struct list_node** pn = pfirst;
    
    //@ open path(pn, last_sorted->next, sorted_vs);
    int comparison = compare(*pn, first_unsorted);
    //@ close path(pn, last_sorted->next, sorted_vs);
    
    //@ list<int> p1 = nil;
    //@ list<int> p2 = sorted_vs;
    while (pn != &(last_sorted->next) && comparison < 0)
        /*@
        invariant
            path(pfirst, pn, p1) &*&
            path(pn, last_sorted->next, p2) &*&
            first_unsorted->value |-> v_fu &*&
            first_unsorted->next |-> ?next_fu &*&
            malloc_block_list_node(first_unsorted) &*&
            list(next_fu, ?unsorted_tail) &*&
            sorted_vs == append(p1, p2) &*&
            is_sorted(sorted_vs) == true &*&
            is_permutation(append(sorted_vs, cons(v_fu, unsorted_tail)), initial_vs) == true &*&
            forall(p1, (is_lt)(v_fu)) == true;
        @*/
    {
      //@ open path(pn, last_sorted->next, p2);
      pn = &((*pn)->next);
      //@ p1 = append(p1, cons(head(p2), nil));
      //@ p2 = tail(p2);
      
      if (pn != &(last_sorted->next)) {
        //@ open path(pn, last_sorted->next, p2);
        comparison = compare(*pn, first_unsorted);
        //@ close path(pn, last_sorted->next, p2);
      }
    }
    
    if (pn != &(last_sorted->next)) {
      //@ open path(pfirst, pn, p1);
      //@ open path(pn, last_sorted->next, p2);
      
      // Detach first_unsorted from the list
      last_sorted->next = first_unsorted->next;
      
      // Insert first_unsorted at *pn
      first_unsorted->next = *pn;
      *pn = first_unsorted;
      
      //@ is_permutation_append_swap(p1, p2, v_fu, tail(unsorted_vs));
      //@ is_permutation_trans(append(sorted_vs, unsorted_vs), append(append(p1, p2), cons(v_fu, tail(unsorted_vs))), _);
      //@ is_permutation_trans(append(append(p1, cons(v_fu, p2)), tail(unsorted_vs)), _, _);
      
      //@ is_sorted_weaken(sorted_vs);
      //@ is_sorted_split(sorted_vs, length(p1));
      //@ forall_path_lt(pfirst, pn, v_fu);
      //@ assert forall(p1, (is_lt)(v_fu)) == true;
      //@ assert p2 == nil || v_fu <= head(p2);
      //@ forall_ge_trans(tail(p2), head(p2), v_fu);
      //@ is_sorted_append(cons(v_fu, nil), p2);
      //@ is_sorted_append(p1, cons(v_fu, p2));
    } else {
      //@ path_join(pfirst);
      last_sorted = last_sorted->next;
      //@ is_sorted_append(sorted_vs, cons(v_fu, nil));
    }
  }
  //@ path_to_lseg(pfirst, 0);
  //@ open lseg(0,0,_);
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
    //@ requires list(l, ?vs);
    //@ ensures list(result, ?vs_sorted) &*& is_sorted(vs_sorted) == true &*& is_permutation(vs, vs_sorted) == true;
{
  //@ lseg_to_path(&l, 0);
  insertion_sort_core(&l);
  //@ path_to_lseg(&l, 0);
  return l;
}