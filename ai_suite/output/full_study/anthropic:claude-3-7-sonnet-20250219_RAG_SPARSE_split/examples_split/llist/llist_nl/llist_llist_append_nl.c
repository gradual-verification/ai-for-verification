#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

/*@
// Define a predicate for a linked list segment
predicate nodes(struct node *first, struct node *last, list<int> values) =
  first == last ?
    values == nil
  :
    first != 0 &*& first->next |-> ?next &*& first->value |-> ?value &*&
    malloc_block_node(first) &*& nodes(next, last, ?tail) &*&
    values == cons(value, tail);

// Define a predicate for the linked list structure
predicate llist(struct llist *list, list<int> values) =
  list->first |-> ?first &*& list->last |-> ?last &*&
  malloc_block_llist(list) &*&
  (first == 0 ?
    values == nil &*& last == 0
  :
    nodes(first, 0, values) &*& last != 0 &*&
    last->next |-> 0 &*& last->value |-> ?lastval &*&
    malloc_block_node(last));
@*/

// TODO: make this function pass the verification
/***
 * Description:
The llist_append function appends the second list to the end of the first list,

@param list1: a single linked list to which another list is appended
@param list2: a single linked list to be appended to the end of list1

It makes sure that list2 is appended to the end of list1.
*/
void llist_append(struct llist *list1, struct llist *list2)
/*@
  requires llist(list1, ?values1) &*& llist(list2, ?values2);
  ensures llist(list1, append(values1, values2));
@*/
{
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  
  /*@
  open llist(list1, values1);
  open llist(list2, values2);
  @*/
  
  if (f2 == l2) {
    /*@
    if (f2 == 0) {
      // list2 is empty, nothing to append
      close llist(list1, values1);
    } else {
      // list2 has only one node
      assert f2->next |-> 0;
      assert f2->value |-> ?f2val;
      
      if (list1->first == 0) {
        // list1 is empty
        list1->first = f2;
        list1->last = f2;
        close nodes(f2, 0, cons(f2val, nil));
        close llist(list1, cons(f2val, nil));
      } else {
        // list1 is not empty
        assert list1->last != 0;
        assert list1->last->next |-> 0;
        list1->last->next = f2;
        list1->last = f2;
        
        // Prove that the resulting list has the expected values
        assert nodes(list1->first, 0, values1);
        close llist(list1, append(values1, cons(f2val, nil)));
      }
    }
    @*/
    free(l2);
    free(list2);
  } else {
    /*@
    if (list1->first == 0) {
      // list1 is empty
      list1->first = f2->next;
      list1->last = l2;
      
      // Extract the value from f2
      assert f2->value |-> ?f2val;
      
      // Prove that the resulting list has the expected values
      assert nodes(f2->next, 0, tail(values2));
      close llist(list1, tail(values2));
    } else {
      // list1 is not empty
      assert list1->last != 0;
      assert list1->last->next |-> 0;
      
      // Connect list1's last node to list2's nodes (skipping f2)
      list1->last->next = f2->next;
      
      // Update list1's last pointer
      list1->last = l2;
      
      // Extract the value from f2
      assert f2->value |-> ?f2val;
      
      // Prove that the resulting list has the expected values
      assert nodes(list1->first, 0, values1);
      assert nodes(f2->next, 0, tail(values2));
      
      // Lemma to help VeriFast understand the structure
      nodes_append(list1->first, 0, values1, f2->next, 0, tail(values2));
      
      close llist(list1, append(values1, tail(values2)));
    }
    @*/
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    free(f2);
    free(list2);
  }
}

/*@
// Helper lemma to prove that appending two node sequences results in the expected values
lemma void nodes_append(struct node *first1, struct node *last1, list<int> values1, 
                        struct node *first2, struct node *last2, list<int> values2)
  requires nodes(first1, last1, values1) &*& nodes(first2, last2, values2) &*& last1 == first2;
  ensures nodes(first1, last2, append(values1, values2));
{
  open nodes(first1, last1, values1);
  if (first1 == last1) {
    close nodes(first1, last2, append(values1, values2));
  } else {
    nodes_append(first1->next, last1, tail(values1), first2, last2, values2);
    close nodes(first1, last2, append(values1, values2));
  }
}
@*/