#include <stdlib.h>

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

  // --- Ghost code for verification ---

  predicate list_full(struct list_node* n; list<struct list_node*> nodes) =
    n == 0 ?
        nodes == nil
    :
        n->value |-> _ &*& n->next |-> ?next &*&
        list_full(next, ?rest_nodes) &*&
        nodes == cons(n, rest_nodes);

  lemma void list_full_to_list_pred(struct list_node* n)
      requires list_full(n, ?nodes);
      ensures list_pred(n);
  {
      open list_full(n, nodes);
      if (n != 0) {
          list_full_to_list_pred(n->next);
      }
      close list_pred(n);
  }

  lemma void list_pred_to_list_full(struct list_node* n)
      requires list_pred(n);
      ensures list_full(n, _);
  {
      open list_pred(n);
      if (n != 0) {
          list_pred_to_list_full(n->next);
      }
      close list_full(n, _);
  }

  predicate lseg_full(struct list_node* from, struct list_node* to; list<struct list_node*> nodes) =
      from == to ?
          nodes == nil
      :
          from != 0 &*&
          from->value |-> _ &*& from->next |-> ?next &*&
          lseg_full(next, to, ?rest_nodes) &*&
          nodes == cons(from, rest_nodes);

  lemma void list_full_split(struct list_node* n, struct list_node* at)
      requires list_full(n, ?nodes) &*& mem(at, nodes) == true;
      ensures lseg_full(n, at, ?prefix_nodes) &*& list_full(at, ?suffix_nodes) &*&
              append(prefix_nodes, suffix_nodes) == nodes;
  {
      open list_full(n, nodes);
      if (n == at) {
          close lseg_full(n, at, nil);
      } else {
          list_full_split(n->next, at);
          close lseg_full(n, at, _);
      }
  }

  lemma void lseg_full_join(struct list_node* from, struct list_node* at)
      requires lseg_full(from, at, ?p1) &*& list_full(at, ?p2);
      ensures list_full(from, append(p1, p2));
  {
      open lseg_full(from, at, p1);
      if (from != at) {
          lseg_full_join(from->next, at);
          close list_full(from, _);
      }
  }

  lemma void lseg_full_unroll(struct list_node* from, struct list_node* to)
    requires lseg_full(from, to, ?nodes) &*& from != to;
    ensures from->value |-> _ &*& from->next |-> ?next &*& lseg_full(next, to, tail(nodes)) &*& nodes == cons(from, tail(nodes));
  {
    open lseg_full(from, to, nodes);
  }

  lemma void lseg_full_roll(struct list_node* from, struct list_node* to)
    requires from != to &*& from->value |-> _ &*& from->next |-> ?next &*& lseg_full(next, to, ?rest_nodes);
    ensures lseg_full(from, to, cons(from, rest_nodes));
  {
    close lseg_full(from, to, cons(from, rest_nodes));
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


void insertion_sort_core(struct list_node** pfirst)
//@ requires *pfirst |-> ?l &*& list_pred(l);
//@ ensures *pfirst |-> ?l0 &*& list_pred(l0);
{
  list_pred_to_list_full(*pfirst);
  if (*pfirst == 0 || (*pfirst)->next == 0) {
    list_full_to_list_pred(*pfirst);
    return;
  }  
  
  struct list_node* last_sorted = *pfirst;
  //@ list_full_split(*pfirst, last_sorted);
  
  while (last_sorted->next != 0)
  /*@
    invariant *pfirst |-> ?head &*&
              exists<list<struct list_node*> >(?sorted_nodes) &*&
              lseg_full(head, last_sorted, ?p1) &*&
              last_sorted->value |-> _ &*& last_sorted->next |-> ?current &*&
              list_full(current, ?unsorted_nodes) &*&
              sorted_nodes == append(p1, cons(last_sorted, nil));
  @*/
  {
    //@ open list_full(last_sorted->next, unsorted_nodes);
    struct list_node* first_unsorted = last_sorted->next;
    
    struct list_node** pn = pfirst;
    //@ lseg_full_roll(head, last_sorted);
    
    int comparison = compare(*pn, first_unsorted);
    while (pn != &(last_sorted->next) && comparison < 0)
    /*@
      invariant *pfirst |-> head &*&
                lseg_full(head, *pn, ?prefix_nodes) &*&
                list_full(*pn, ?suffix_nodes) &*&
                mem(last_sorted, suffix_nodes) == true &*&
                last_sorted->next |-> first_unsorted &*&
                first_unsorted->value |-> _ &*& first_unsorted->next |-> ?rest &*&
                list_full(rest, tail(unsorted_nodes));
    @*/
    {
      //@ list_full_split(*pn, last_sorted);
      //@ open list_full(*pn, _);
      pn = &((*pn)->next);
      //@ lseg_full_join(head, *pn);
      
      if (pn != &(last_sorted->next)) {
        comparison = compare(*pn, first_unsorted);
      }
    }
    
    //@ list_full_split(*pn, last_sorted);
    
    if (pn != &(last_sorted->next)) {
      //@ open list_full(first_unsorted, _);
      last_sorted->next = first_unsorted->next;
      first_unsorted->next = *pn;
      *pn = first_unsorted;
      
      //@ lseg_full_join(head, last_sorted);
    } else {
      last_sorted = last_sorted->next;
      //@ lseg_full_join(head, last_sorted);
    }
  }
  
  //@ lseg_full_join(*pfirst, last_sorted);
  //@ list_full_to_list_pred(*pfirst);
}



// TODO: make this function pass the verification
struct list_node* insertion_sort(struct list_node* l)
//@ requires list_pred(l);
//@ ensures list_pred(result);
{
  insertion_sort_core(&l);
  return l;
}