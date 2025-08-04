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

  // A list segment from 'from' (inclusive) to 'to' (exclusive).
  predicate lseg(struct list_node* from, struct list_node* to) =
    from == to ?
      true
    :
      from->value |-> _ &*& from->next |-> ?next &*& lseg(next, to);

  lemma void lseg_append(struct list_node* n1, struct list_node* n2, struct list_node* n3)
    requires lseg(n1, n2) &*& lseg(n2, n3);
    ensures lseg(n1, n3);
  {
    open lseg(n1, n2);
    if (n1 != n2) {
      lseg_append(n1->next, n2, n3);
      close lseg(n1, n3);
    }
  }

  // A predicate for the "context" of a pointer 'p_hole' within a list.
  // It owns the path of pointers from 'p_start' to 'p_hole'.
  // 'start_node' is the value of '*p_start'.
  predicate lseg_context(struct list_node** p_start, struct list_node** p_hole, struct list_node* start_node) =
    p_start == p_hole ?
      *p_start |-> start_node
    :
      *p_start |-> start_node &*&
      start_node->value |-> _ &*& start_node->next |-> ?next &*&
      lseg_context(&(start_node->next), p_hole, next);

  lemma void lseg_context_open(struct list_node** p_start, struct list_node** p_hole)
    requires lseg_context(p_start, p_hole, ?start_node) &*& p_start != p_hole;
    ensures *p_start |-> start_node &*& start_node->value |-> _ &*& start_node->next |-> ?next &*&
            lseg_context(&(start_node->next), p_hole, next);
  {
    open lseg_context(p_start, p_hole, start_node);
  }

  lemma void lseg_context_close(struct list_node** p_start, struct list_node* start_node)
    requires *p_start |-> start_node &*& start_node->value |-> _ &*& start_node->next |-> ?next &*&
             lseg_context(&(start_node->next), ?p_hole, next);
    ensures lseg_context(p_start, p_hole, start_node);
  {
    close lseg_context(p_start, p_hole, start_node);
  }

  lemma void lseg_context_to_lseg(struct list_node** p_start, struct list_node** p_hole)
    requires lseg_context(p_start, p_hole, ?start_node);
    ensures lseg_context(p_start, p_hole, start_node) &*& lseg(start_node, *p_hole);
  {
    open lseg_context(p_start, p_hole, start_node);
    if (p_start == p_hole) {
      close lseg(*p_hole, *p_hole);
    } else {
      lseg_context_to_lseg(&(start_node->next), p_hole);
      close lseg(start_node, *p_hole);
    }
    close lseg_context(p_start, p_hole, start_node);
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
  if (*pfirst == 0) {
    return;
  }
  
  struct list_node* last_sorted = *pfirst;
  //@ open list_pred(l);
  //@ close lseg(l, l);

  while (last_sorted->next != 0)
    /*@
    invariant
      *pfirst |-> ?head &*&
      lseg(head, last_sorted) &*&
      last_sorted->value |-> _ &*& last_sorted->next |-> ?first_unsorted &*&
      first_unsorted != 0 &*&
      list_pred(first_unsorted);
    @*/
  {
    struct list_node* to_insert = last_sorted->next;
    //@ open list_pred(to_insert);
    //@ assert to_insert->value |-> ?v_ti &*& to_insert->next |-> ?n_ti &*& list_pred(n_ti);

    struct list_node** pn = pfirst;
    //@ close lseg_context(pfirst, pfirst, head);

    //@ lseg_context_to_lseg(pfirst, pfirst);
    //@ open lseg(head, head);
    //@ lseg_append(head, head, last_sorted);

    int comparison = compare(*pn, to_insert);
    //@ open lseg(head, last_sorted);
    //@ close lseg(head, last_sorted);

    while (pn != &(last_sorted->next) && comparison < 0)
      /*@
      invariant
        *pfirst |-> head &*&
        lseg_context(pfirst, pn, head) &*&
        lseg(*pn, last_sorted) &*&
        last_sorted->value |-> _ &*& last_sorted->next |-> to_insert &*&
        to_insert->value |-> v_ti &*& to_insert->next |-> n_ti &*& list_pred(n_ti);
      @*/
    {
      //@ lseg_context_open(pfirst, pn);
      //@ struct list_node* current_node = *pn;
      //@ open lseg(current_node, last_sorted);
      pn = &((*pn)->next);
      //@ lseg_context_close(pfirst, head);

      if (pn != &(last_sorted->next)) {
        //@ struct list_node* next_node = *pn;
        //@ open lseg(next_node, last_sorted);
        comparison = compare(next_node, to_insert);
        //@ close lseg(next_node, last_sorted);
      }
    }

    if (pn != &(last_sorted->next)) {
      //@ lseg_context_to_lseg(pfirst, pn);
      //@ open lseg_context(pfirst, pn, head);
      //@ struct list_node* insertion_point = *pn;
      //@ assert lseg(head, insertion_point);

      last_sorted->next = to_insert->next;
      to_insert->next = *pn;
      *pn = to_insert;

      //@ close lseg(to_insert, insertion_point);
      //@ lseg_append(head, to_insert, insertion_point);
      //@ lseg_append(head, insertion_point, last_sorted);
      //@ close list_pred(n_ti);
    } else {
      //@ open lseg_context(pfirst, &(last_sorted->next), head);
      //@ lseg_context_to_lseg(pfirst, &(last_sorted->next));
      //@ assert lseg(head, to_insert);
      //@ close lseg(last_sorted, to_insert);
      //@ lseg_append(head, last_sorted, to_insert);
      last_sorted = to_insert;
    }
  }
  
  //@ *pfirst |-> ?h;
  //@ lseg(h, last_sorted) &*& last_sorted->value |-> _ &*& last_sorted->next |-> 0 &*& list_pred(0);
  //@ open list_pred(0);
  //@ close lseg(last_sorted, 0);
  //@ lseg_append(h, last_sorted, 0);
  //@ close list_pred(h);
}



// TODO: make this function pass the verification
struct list_node* insertion_sort(struct list_node* l)
//@ requires list_pred(l);
//@ ensures list_pred(result);
{
  insertion_sort_core(&l);
  return l;
}