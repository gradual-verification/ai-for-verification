#include "prelude.h"

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

  // A segment of a list, from `from` (inclusive) to `to` (exclusive).
  predicate list_pred_segment(struct list_node* from, struct list_node* to) =
    from == to ?
      true
    :
      from != 0 &*&
      from->value |-> _ &*& from->next |-> ?next &*&
      list_pred_segment(next, to);

  // Pure function to check reachability.
  fixpoint bool is_reachable(struct list_node* from, struct list_node* to) {
    return from == to ? true : (from == 0 ? false : is_reachable(from->next, to));
  }

  // Lemma to split a list into a segment and a remainder list.
  lemma void list_pred_split(struct list_node* from, struct list_node* to)
    requires list_pred(from) &*& is_reachable(from, to) == true;
    ensures list_pred_segment(from, to) &*& list_pred(to);
  {
    open list_pred(from);
    if (from != to) {
      list_pred_split(from->next, to);
      close list_pred_segment(from, to);
    } else {
      close list_pred_segment(to, to);
    }
  }

  // Lemma to join a segment and a list back into one list.
  lemma void list_pred_join(struct list_node* from, struct list_node* to)
    requires list_pred_segment(from, to) &*& list_pred(to);
    ensures list_pred(from);
  {
    open list_pred_segment(from, to);
    if (from != to) {
      list_pred_join(from->next, to);
      close list_pred(from);
    }
  }

  // A path of `next` pointers, from `start_pp` to `end_pp`.
  // Owns the list nodes and the pointers in the path.
  predicate list_path(struct list_node** start_pp, struct list_node** end_pp, struct list_node* start_node) =
    start_pp == end_pp ?
      true
    :
      *start_pp |-> start_node &*& start_node != 0 &*&
      start_node->value |-> _ &*& start_node->next |-> ?next_node &*&
      list_path(&(start_node->next), end_pp, next_node);

  // Lemma to join a path with the rest of the list.
  lemma void list_path_join(struct list_node** start_pp, struct list_node** end_pp, struct list_node* start_node)
    requires list_path(start_pp, end_pp, start_node) &*& *end_pp |-> ?end_node &*& list_pred(end_node);
    ensures list_pred(start_node);
  {
    open list_path(start_pp, end_pp, start_node);
    if (start_pp != end_pp) {
      list_path_join(&(start_node->next), end_pp, start_node->next);
      close list_pred(start_node);
    }
  }

  // Lemma to establish reachability along a path.
  lemma void list_path_is_reachable(struct list_node** start_pp, struct list_node** end_pp, struct list_node* start_node)
    requires list_path(start_pp, end_pp, start_node) &*& *end_pp |-> ?end_node;
    ensures list_path(start_pp, end_pp, start_node) &*& *end_pp |-> end_node &*& is_reachable(start_node, end_node) == true;
  {
    open list_path(start_pp, end_pp, start_node);
    if (start_pp != end_pp) {
      list_path_is_reachable(&(start_node->next), end_pp, start_node->next);
      close list_path(start_pp, end_pp, start_node);
    }
  }
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
//@ ensures *pfirst |-> ?l0 &*& list_pred(l0);
{
  if (*pfirst == 0) {
    return;
  }  
  
  struct list_node* last_sorted = *pfirst;
  while (last_sorted->next != 0)
    /*@
    invariant *pfirst |-> ?head &*& list_pred(head) &*&
              last_sorted != 0 &*& is_reachable(head, last_sorted) == true;
    @*/
  {
    struct list_node* node_to_insert = last_sorted->next;
    //@ list_pred_split(head, node_to_insert);
    //@ open list_pred(node_to_insert);
    //@ assert node_to_insert->value |-> ?v_ins &*& node_to_insert->next |-> ?rest &*& list_pred(rest);
    
    struct list_node** pn = pfirst;
    
    //@ list_path_is_reachable(pfirst, pfirst, head);
    //@ list_pred_split(head, head);
    //@ close list_path(pfirst, pfirst, head);
    
    int comparison = compare(*pn, node_to_insert);
    
    while (pn != &(last_sorted->next) && comparison < 0)
      /*@
      invariant *pfirst |-> head &*&
                list_path(pfirst, pn, head) &*&
                *pn |-> ?curr_node &*&
                is_reachable(curr_node, node_to_insert) == true &*&
                list_pred_segment(curr_node, node_to_insert) &*&
                node_to_insert->value |-> v_ins &*& node_to_insert->next |-> rest &*&
                list_pred(rest);
      @*/
    {
      //@ open list_path(pfirst, pn, head);
      //@ open list_pred_segment(curr_node, node_to_insert);
      pn = &((*pn)->next);
      //@ close list_path(pfirst, pn, head);
      
      if (pn != &(last_sorted->next)) {
        //@ list_path_is_reachable(pfirst, pn, head);
        //@ list_pred_split(head, *pn);
        comparison = compare(*pn, node_to_insert);
        //@ list_pred_join(head, *pn);
      }
    }
    
    if (pn != &(last_sorted->next)) {
      struct list_node* first_unsorted = last_sorted->next;
      //@ list_pred_split(head, last_sorted);
      //@ open list_pred(last_sorted);
      last_sorted->next = first_unsorted->next;
      //@ list_pred_join(last_sorted, rest);
      //@ list_pred_join(head, last_sorted);
      
      //@ list_path_is_reachable(pfirst, pn, head);
      //@ list_pred_split(head, *pn);
      first_unsorted->next = *pn;
      //@ close list_pred(first_unsorted);
      *pn = first_unsorted;
      //@ list_path_join(pfirst, pn, head);
    } else {
      //@ list_pred_join(head, node_to_insert);
      last_sorted = last_sorted->next;
    }
  }
}