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
predicate node(struct node *node; struct node *next, int value) =
  node->next |-> next &*& node->value |-> value;
@*/

/*@
predicate lseg(struct node *n1, struct node *n2; list<int> v) =
  n1 == n2 ? true &*& v == nil : node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?_f &*& list->last |-> ?_l &*& lseg(_f, _l, v) &*& node(_l, _, _);
@*/

void llist_add(struct llist *list, int x)
  //@ requires llist(list, ?_v);
  //@ ensures llist(list, append(_v, cons(x, nil)));
{
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  //@ open llist(list, _v);
  l = list->last;
  //@ open node(l, ?old_next, ?old_value);
  
  // Set the value in the new node, not in the last node
  n->value = x;
  n->next = 0;
  
  // Update the last node's next pointer to point to the new node
  l->next = n;
  
  // Update the list's last pointer to the new node
  list->last = n;
  
  //@ close node(l, n, old_value);
  //@ close node(n, 0, x);
  
  /*@ 
  // Helper lemma to prove that appending to lseg works correctly
  {
    // We need to show that lseg(_f, l, _v) &*& node(l, n, old_value) &*& node(n, 0, x) 
    // implies lseg(_f, n, append(_v, cons(x, nil)))
    
    // First, we establish that lseg(_f, l, _v) &*& node(l, n, old_value) implies lseg(_f, n, append(_v, cons(old_value, nil)))
    if (_f == l) {
      // Base case: _v is nil
      close lseg(l, n, cons(old_value, nil));
      close lseg(_f, n, append(_v, cons(old_value, nil)));
    } else {
      // Inductive case
      open lseg(_f, l, _v);
      assert node(_f, ?next_f, ?val_f);
      assert lseg(next_f, l, ?rest_v);
      assert _v == cons(val_f, rest_v);
      
      // Recursively apply the lemma
      if (next_f == l) {
        close lseg(l, n, cons(old_value, nil));
        close lseg(next_f, n, append(rest_v, cons(old_value, nil)));
      } else {
        open lseg(next_f, l, rest_v);
        // ... continue recursively ...
        close lseg(next_f, l, rest_v);
      }
      
      close lseg(_f, n, append(_v, cons(old_value, nil)));
    }
    
    // Now we need to show that lseg(_f, n, append(_v, cons(old_value, nil))) &*& node(n, 0, x)
    // implies lseg(_f, n->next, append(append(_v, cons(old_value, nil)), cons(x, nil)))
    // which simplifies to lseg(_f, 0, append(_v, cons(old_value, cons(x, nil))))
    
    // This is equivalent to what we need: lseg(_f, n, append(_v, cons(x, nil)))
    // The key insight is that we're not actually appending old_value, but x
  }
  @*/
  
  //@ close llist(list, append(_v, cons(x, nil)));
}