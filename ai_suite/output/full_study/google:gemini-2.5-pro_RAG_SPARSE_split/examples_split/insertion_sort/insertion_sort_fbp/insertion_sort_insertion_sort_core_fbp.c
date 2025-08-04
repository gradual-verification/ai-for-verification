#include "stdlib.h"

struct list_node {
  int value;
  struct list_node* next;
};

/*@
  // --- Predicates and Fixpoints for Verification ---

  fixpoint bool sorted(list<int> vs) {
    switch (vs) {
      case nil: return true;
      case cons(h, t): return forall(t, (fixpoint(int, bool))(x) { return h <= x; }) && sorted(t);
    }
  }

  fixpoint int count_elem<t>(list<t> l, t e) {
    switch (l) {
        case nil: return 0;
        case cons(h, t): return (h == e ? 1 : 0) + count_elem(t, e);
    }
  }

  fixpoint bool multiset_eq<t>(list<t> l1, list<t> l2) {
    return forall(l1, (fixpoint(t, bool))(e) { return count_elem(l1, e) == count_elem(l2, e); }) &&
           forall(l2, (fixpoint(t, bool))(e) { return count_elem(l1, e) == count_elem(l2, e); });
  }

  predicate list(struct list_node* n; list<int> vs) =
    n == 0 ?
      vs == nil
    :
      n->value |-> ?v &*& n->next |-> ?next &*&
      list(next, ?vst) &*& vs == cons(v, vst);

  predicate lseg(struct list_node* from, struct list_node* to; list<int> vs) =
    from == to ?
      vs == nil
    :
      from->value |-> ?v &*& from->next |-> ?next &*&
      lseg(next, to, ?vst) &*& vs == cons(v, vst);

  // Represents the prefix of a list from `pp_start` up to the pointer `pp_hole`.
  // Owns the `value` fields and the chain of `next` pointers forming the prefix.
  predicate list_prefix(struct list_node** pp_start, struct list_node** pp_hole; list<int> vs) =
    pp_start == pp_hole ?
      vs == nil
    :
      *pp_start |-> ?head &*& head != 0 &*& head->value |-> ?v &*&
      list_prefix(&(head->next), pp_hole, ?vst) &*& vs == cons(v, vst);

  // --- Lemmas ---

  lemma void list_pred_to_list(struct list_node* n)
    requires list_pred(n);
    ensures list(n, ?vs);
  {
    open list_pred(n);
    if (n == 0) {
      close list(0, nil);
    } else {
      list_pred_to_list(n->next);
      close list(n, cons(n->value, ?vst));
    }
  }

  lemma void list_to_list_pred(struct list_node* n)
    requires list(n, _);
    ensures list_pred(n);
  {
    open list(n, _);
    if (n != 0) {
      list_to_list_pred(n->next);
    }
    close list_pred(n);
  }

  lemma void lseg_to_list_prefix_and_lseg(struct list_node** pp_start, struct list_node** pp_hole, struct list_node* start_node)
    requires *pp_start |-> start_node &*& lseg(start_node, ?end_node, ?vs) &*& *pp_hole |-> end_node;
    ensures list_prefix(pp_start, pp_hole, ?prefix_vs) &*& lseg(end_node, end_node, ?suffix_vs) &*& vs == append(prefix_vs, suffix_vs);
  {
    open lseg(start_node, end_node, vs);
    if (pp_start == pp_hole) {
      close list_prefix(pp_start, pp_hole, nil);
      close lseg(end_node, end_node, nil);
    } else {
      lseg_to_list_prefix_and_lseg(&((*pp_start)->next), pp_hole, (*pp_start)->next);
      close list_prefix(pp_start, pp_hole, cons((*pp_start)->value, ?prefix_vs));
    }
  }

  lemma void join_prefix_and_lseg(struct list_node** pp_start, struct list_node** pp_hole, struct list_node* start_node)
    requires list_prefix(pp_start, pp_hole, ?prefix_vs) &*& *pp_hole |-> ?hole_node &*& lseg(hole_node, 0, ?suffix_vs) &*& *pp_start |-> start_node;
    ensures list(start_node, append(prefix_vs, suffix_vs));
  {
    open list_prefix(pp_start, pp_hole, prefix_vs);
    if (pp_start == pp_hole) {
      close list(hole_node, suffix_vs);
    } else {
      join_prefix_and_lseg(&((*pp_start)->next), pp_hole, (*pp_start)->next);
      close list(start_node, append(prefix_vs, suffix_vs));
    }
  }

  lemma void extend_prefix(struct list_node** pp_start, struct list_node** pp_hole)
    requires list_prefix(pp_start, pp_hole, ?vs) &*& *pp_hole |-> ?hole_node &*& hole_node != 0 &*& hole_node->value |-> ?v;
    ensures list_prefix(pp_start, &(hole_node->next), append(vs, cons(v, nil)));
  {
    open list_prefix(pp_start, pp_hole, vs);
    if (pp_start != pp_hole) {
      extend_prefix(&((*pp_start)->next), pp_hole);
    }
    close list_prefix(pp_start, &(hole_node->next), append(vs, cons(v, nil)));
  }

  lemma void forall_le_trans(list<int> vs, int v1, int v2)
    requires forall(vs, (fixpoint(int, bool))(x) { return x <= v1; }) == true &*& v1 <= v2;
    ensures forall(vs, (fixpoint(int, bool))(x) { return x <= v2; }) == true;
  {
    switch(vs) {
      case nil:
      case cons(h, t):
        forall_le_trans(t, v1, v2);
    }
  }

  lemma void sorted_insert_lemma(list<int> prefix, int v, list<int> suffix)
    requires sorted(append(prefix, suffix)) == true &*& forall(prefix, (fixpoint(int, bool))(x) { return x <= v; }) == true &*& forall(suffix, (fixpoint(int, bool))(x) { return v <= x; }) == true;
    ensures sorted(append(prefix, cons(v, suffix))) == true;
  {
    switch(prefix) {
      case nil:
      case cons(h, t):
        forall_le_trans(t, h, v);
        sorted_insert_lemma(t, v, suffix);
    }
  }

  lemma void multiset_eq_lem(list<int> l, int v, list<int> prefix, list<int> suffix)
    requires l == append(prefix, suffix);
    ensures multiset_eq(l, append(prefix, cons(v, remove(v, l)))) == false; // This is not what I need.
    // The multiset equality is preserved by reordering, which is what happens.
    // A lemma like multiset_eq(append(l1, l2), append(l2, l1)) would be useful.
    // But here it's an insertion.
    // multiset_eq(append(sorted_part, cons(v_ins, rest)), append(new_sorted_part, rest))
    // new_sorted_part = insert(v_ins, sorted_part)
    // This holds by definition of multiset equality.

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


// TODO: make this function pass the verification
void insertion_sort_core(struct list_node** pfirst)
//@ requires *pfirst |-> ?l &*& list_pred(l);
//@ ensures *pfirst |-> ?l0 &*& list_pred(l0) &*& list(l0, ?vs) &*& sorted(vs) == true;
{
  list_pred_to_list(l);
  //@ assert list(l, ?initial_vs);
  if (*pfirst == 0) {
    //@ list_to_list_pred(l);
    return;
  }
  if ((*pfirst)->next == 0) {
    //@ list_to_list_pred(l);
    return;
  }

  struct list_node* last_sorted = *pfirst;
  //@ open list(l, initial_vs);
  //@ close lseg(l, l, nil);
  //@ multiset_eq(initial_vs, initial_vs);

  while (last_sorted->next != 0)
    /*@
    invariant
      *pfirst |-> ?head &*&
      lseg(head, last_sorted, ?sorted_prefix_vs) &*&
      last_sorted->value |-> ?v_last &*&
      last_sorted->next |-> ?first_unsorted &*&
      list(first_unsorted, ?unsorted_vs) &*&
      let sorted_vs = append(sorted_prefix_vs, cons(v_last, nil)) &*&
      sorted(sorted_vs) == true &*&
      multiset_eq(append(sorted_vs, unsorted_vs), initial_vs) == true;
    @*/
  {
    //@ open list(last_sorted->next, unsorted_vs);
    struct list_node* node_to_insert = last_sorted->next;
    //@ int v_ins = node_to_insert->value;
    //@ struct list_node* rest_unsorted = node_to_insert->next;
    //@ list<int> rest_unsorted_vs = tail(unsorted_vs);
    //@ list<int> sorted_vs = append(sorted_prefix_vs, cons(v_last, nil));

    struct list_node** pn = pfirst;
    //@ lseg_to_list_prefix_and_lseg(pfirst, &last_sorted, head);
    //@ assert lseg(last_sorted, last_sorted, ?tmp_vs) &*& tmp_vs == nil;
    //@ close lseg(last_sorted, node_to_insert, cons(v_last, nil));

    int comparison = compare(*pn, node_to_insert);
    while (pn != &(last_sorted->next) && comparison < 0)
      /*@
      invariant
        *pfirst |-> head &*&
        list_prefix(pfirst, pn, ?prefix_vs) &*&
        *pn |-> ?pn_node &*&
        lseg(pn_node, node_to_insert, ?suffix_vs) &*&
        node_to_insert->value |-> ?v_ins2 &*& node_to_insert->next |-> ?rest_unsorted2 &*&
        list(rest_unsorted2, ?rest_unsorted_vs2) &*&
        let current_sorted_vs = append(prefix_vs, suffix_vs) &*&
        sorted(current_sorted_vs) == true &*&
        forall(prefix_vs, (fixpoint(int, bool))(v) { return v < v_ins2; }) == true &*&
        multiset_eq(append(current_sorted_vs, cons(v_ins2, rest_unsorted_vs2)), initial_vs) == true;
      @*/
    {
      //@ open lseg(pn_node, node_to_insert, suffix_vs);
      //@ extend_prefix(pfirst, pn);
      pn = &((*pn)->next);
      if (pn != &(last_sorted->next)) {
        comparison = compare(*pn, node_to_insert);
      }
    }

    if (pn != &(last_sorted->next)) {
      //@ open lseg(*pn, node_to_insert, ?suffix_vs);
      //@ assert *pn |-> ?pn_node;
      //@ int v_pn = pn_node->value;
      //@ assert v_pn >= v_ins;
      struct list_node* first_unsorted = last_sorted->next;
      last_sorted->next = first_unsorted->next;
      first_unsorted->next = *pn;
      *pn = first_unsorted;

      //@ list<int> new_sorted_vs = append(prefix_vs, cons(v_ins, suffix_vs));
      //@ sorted_insert_lemma(prefix_vs, v_ins, suffix_vs);
      //@ multiset_eq(append(sorted_vs, unsorted_vs), initial_vs);
      //@ multiset_eq(append(append(prefix_vs, suffix_vs), cons(v_ins, rest_unsorted_vs)), initial_vs);
      //@ multiset_eq(append(new_sorted_vs, rest_unsorted_vs), initial_vs);
      //@ join_prefix_and_lseg(pfirst, &last_sorted->next, head);
    } else {
      //@ assert pn == &last_sorted->next;
      //@ assert *pn == node_to_insert;
      //@ forall_le_trans(prefix_vs, v_last, v_ins);
      //@ sorted(append(prefix_vs, cons(v_last, cons(v_ins, nil))));
      last_sorted = last_sorted->next;
      //@ close lseg(head, last_sorted, append(prefix_vs, cons(v_last, nil)));
    }
  }
  //@ list_to_list_pred(*pfirst);
  //@ list(l0, ?vs);
}