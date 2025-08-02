#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

struct iter {
    struct node *current;
};

/*@
// Define predicates for linked list nodes and the list structure
predicate node(struct node *n, int v, struct node *next) =
    n != 0 &*& n->value |-> v &*& n->next |-> next &*& malloc_block_node(n);

predicate llist(struct llist *list, list<int> values) =
    list != 0 &*&
    list->first |-> ?first &*&
    list->last |-> ?last &*&
    malloc_block_llist(list) &*&
    llist_nodes(first, last, values) &*&
    (last != 0 ? last->next |-> 0 : first == 0);

// Recursive predicate to represent a chain of nodes
predicate llist_nodes(struct node *first, struct node *last, list<int> values) =
    first == 0 ?
        values == nil &*& last == 0
    :
        first != 0 &*&
        node(first, head(values), ?next) &*&
        (next == 0 ?
            last == first &*& tail(values) == nil
        :
            llist_nodes(next, last, tail(values))
        );
@*/

// TODO: make this function pass the verification
/***
 * Description:
The list_add function adds an element to the end of the linked list,

@param list: a single linked list
@param x: the element to be added

It makes sure that the list has added x as its last element.
*/
void llist_add(struct llist *list, int x)
/*@
    requires llist(list, ?values);
    ensures llist(list, append(values, cons(x, nil)));
@*/
{
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  //@ open llist(list, values);
  l = list->last;
  
  //@ if (l == 0) {
  //@   open llist_nodes(0, 0, nil);
  //@ } else {
  //@   open llist_nodes(list->first, l, values);
  //@ }
  
  n->next = 0;
  n->value = x;
  
  if (l == 0) {
    // Empty list case
    list->first = n;
    list->last = n;
    //@ close node(n, x, 0);
    //@ close llist_nodes(n, n, cons(x, nil));
  } else {
    // Non-empty list case
    l->next = n;
    list->last = n;
    //@ close node(n, x, 0);
    
    /*@ 
    // Helper lemma to reconstruct the list
    {
      struct node *curr = list->first;
      list<int> prefix = nil;
      
      while (curr != l)
        invariant llist_nodes(list->first, ?mid, take(length(prefix), values)) &*& 
                  node(mid, nth(length(prefix), values), curr) &*&
                  prefix == take(length(prefix), values) &*&
                  length(prefix) < length(values);
      {
        open llist_nodes(list->first, mid, take(length(prefix), values));
        open node(mid, nth(length(prefix), values), curr);
        prefix = append(prefix, cons(nth(length(prefix), values), nil));
        close node(mid, nth(length(prefix) - 1, values), curr);
        close llist_nodes(list->first, curr, prefix);
      }
      
      // Now curr == l
      open llist_nodes(list->first, l, values);
      close node(l, nth(length(values) - 1, values), n);
      close llist_nodes(n, n, cons(x, nil));
      close llist_nodes(list->first, n, append(values, cons(x, nil)));
    }
    @*/
  }
  
  //@ close llist(list, append(values, cons(x, nil)));
}
#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

struct iter {
    struct node *current;
};

/*@
// Define predicates for linked list nodes and the list structure
predicate node(struct node *n, int v, struct node *next) =
    n != 0 &*& n->value |-> v &*& n->next |-> next &*& malloc_block_node(n);

predicate llist(struct llist *list, list<int> values) =
    list != 0 &*&
    list->first |-> ?first &*&
    list->last |-> ?last &*&
    malloc_block_llist(list) &*&
    llist_nodes(first, last, values) &*&
    (last != 0 ? last->next |-> 0 : first == 0);

// Recursive predicate to represent a chain of nodes
predicate llist_nodes(struct node *first, struct node *last, list<int> values) =
    first == 0 ?
        values == nil &*& last == 0
    :
        first != 0 &*&
        node(first, head(values), ?next) &*&
        (next == 0 ?
            last == first &*& tail(values) == nil
        :
            llist_nodes(next, last, tail(values))
        );
@*/

// TODO: make this function pass the verification
/***
 * Description:
The list_add function adds an element to the end of the linked list,

@param list: a single linked list
@param x: the element to be added

It makes sure that the list has added x as its last element.
*/
void llist_add(struct llist *list, int x)
/*@
    requires llist(list, ?values);
    ensures llist(list, append(values, cons(x, nil)));
@*/
{
  //@ open llist(list, values);
  struct node *l = list->last;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  
  n->next = 0;
  n->value = x;
  
  if (l == 0) {
    // Empty list case
    //@ open llist_nodes(0, 0, nil);
    list->first = n;
    list->last = n;
    //@ close node(n, x, 0);
    //@ close llist_nodes(n, n, cons(x, nil));
  } else {
    // Non-empty list case
    l->next = n;
    list->last = n;
    
    /*@
    // Helper lemma to reconstruct the list with the new node
    lemma void append_node(struct node *first, struct node *last, list<int> vs, int x)
      requires llist_nodes(first, last, vs) &*& last->next |-> ?n &*& node(n, x, 0);
      ensures llist_nodes(first, n, append(vs, cons(x, nil)));
    {
      open llist_nodes(first, last, vs);
      if (first == last) {
        close node(first, head(vs), n);
        close llist_nodes(n, n, cons(x, nil));
        close llist_nodes(first, n, append(vs, cons(x, nil)));
      } else {
        append_node(first->next, last, tail(vs), x);
        close node(first, head(vs), first->next);
        close llist_nodes(first, n, append(vs, cons(x, nil)));
      }
    }
    @*/
    
    //@ close node(n, x, 0);
    //@ append_node(list->first, l, values, x);
  }
  
  //@ close llist(list, append(values, cons(x, nil)));
}
#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

struct iter {
    struct node *current;
};

/*@
// Define predicates for linked list nodes and the list structure
predicate node(struct node *n, int v, struct node *next) =
    n != 0 &*& n->value |-> v &*& n->next |-> next &*& malloc_block_node(n);

predicate llist(struct llist *list, list<int> values) =
    list != 0 &*&
    list->first |-> ?first &*&
    list->last |-> ?last &*&
    malloc_block_llist(list) &*&
    llist_nodes(first, last, values) &*&
    (last == 0 ? first == 0 : last->next |-> 0);

// Recursive predicate to represent a chain of nodes
predicate llist_nodes(struct node *first, struct node *last, list<int> values) =
    first == 0 ?
        values == nil &*& last == 0
    :
        first != 0 &*&
        node(first, head(values), ?next) &*&
        (next == 0 ?
            last == first &*& tail(values) == nil
        :
            llist_nodes(next, last, tail(values))
        );

// Helper lemma to reconstruct the list with the new node
lemma void append_node(struct node *first, struct node *last, list<int> vs, int x, struct node *n)
  requires llist_nodes(first, last, vs) &*& last != 0 &*& last->next |-> 0 &*& 
           n != 0 &*& n->value |-> x &*& n->next |-> 0 &*& malloc_block_node(n);
  ensures llist_nodes(first, n, append(vs, cons(x, nil))) &*& n->next |-> 0;
{
  open llist_nodes(first, last, vs);
  if (first == last) {
    last->next = n;
    close node(first, head(vs), n);
    close llist_nodes(n, n, cons(x, nil));
    close llist_nodes(first, n, append(vs, cons(x, nil)));
  } else {
    struct node *next = 0;
    open node(first, head(vs), ?next0);
    next = next0;
    close node(first, head(vs), next);
    append_node(next, last, tail(vs), x, n);
    close llist_nodes(first, n, append(vs, cons(x, nil)));
  }
}
@*/

void llist_add(struct llist *list, int x)
/*@
    requires llist(list, ?values);
    ensures llist(list, append(values, cons(x, nil)));
@*/
{
  //@ open llist(list, values);
  struct node *l = list->last;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  
  n->next = 0;
  n->value = x;
  
  if (l == 0) {
    // Empty list case
    //@ open llist_nodes(0, 0, nil);
    list->first = n;
    list->last = n;
    //@ close node(n, x, 0);
    //@ close llist_nodes(n, n, cons(x, nil));
  } else {
    // Non-empty list case
    l->next = n;
    list->last = n;
    
    //@ append_node(list->first, l, values, x, n);
  }
  
  //@ close llist(list, append(values, cons(x, nil)));
}
#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

struct iter {
    struct node *current;
};

/*@
// Define predicates for nodes and lists
predicate nodes(struct node *first, struct node *last, list<int> values) =
    first == 0 ?
        values == nil &*& last == 0
    :
        first->value |-> head(values) &*& 
        first->next |-> ?next &*& 
        malloc_block_node(first) &*&
        (next == 0 ?
            last == first &*& tail(values) == nil
        :
            nodes(next, last, tail(values))
        );

predicate llist(struct llist *list, list<int> values) =
    list->first |-> ?first &*&
    list->last |-> ?last &*&
    malloc_block_llist(list) &*&
    nodes(first, last, values) &*&
    (last == 0 ? first == 0 : last->next |-> 0);
@*/

void llist_add(struct llist *list, int x)
/*@
    requires llist(list, ?values);
    ensures llist(list, append(values, cons(x, nil)));
@*/
{
  //@ open llist(list, values);
  struct node *l = list->last;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  
  n->next = 0;
  n->value = x;
  
  if (l == 0) {
    // Empty list case
    //@ open nodes(0, 0, nil);
    list->first = n;
  } else {
    // Non-empty list case
    l->next = n;
  }
  list->last = n;
  
  /*@
  // Helper lemma to reconstruct the list
  lemma void append_to_nodes(struct node *first, struct node *last, list<int> vs, struct node *n, int x)
    requires nodes(first, last, vs) &*& last != 0 &*& last->next |-> n &*& 
             n != 0 &*& n->value |-> x &*& n->next |-> 0 &*& malloc_block_node(n);
    ensures nodes(first, n, append(vs, cons(x, nil)));
  {
    open nodes(first, last, vs);
    if (first == last) {
      close nodes(n, n, cons(x, nil));
      close nodes(first, n, append(vs, cons(x, nil)));
    } else {
      append_to_nodes(first->next, last, tail(vs), n, x);
      close nodes(first, n, append(vs, cons(x, nil)));
    }
  }
  @*/
  
  if (l == 0) {
    //@ close nodes(n, n, cons(x, nil));
  } else {
    //@ append_to_nodes(list->first, l, values, n, x);
  }
  
  //@ close llist(list, append(values, cons(x, nil)));
}
#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node