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
predicate nodes(struct node *node, list<int> values) =
  node == 0 ?
    values == nil
  :
    node->value |-> ?v &*& node->next |-> ?next &*& malloc_block_node(node) &*&
    nodes(next, ?tail_values) &*& values == cons(v, tail_values);

// Define a predicate for the llist structure
predicate llist(struct llist *list, list<int> values) =
  list->first |-> ?first &*& list->last |-> ?last &*& malloc_block_llist(list) &*&
  nodes(first, values) &*&
  (first == 0 ? last == 0 : true) &*&
  (first != 0 && last != 0 ? last->next |-> 0 : true);
@*/

/***
 * Description:
The create_llist function allocates an empty linked list with a node as both the first and last of the linked list.

It makes sure that the return value is an empty list. 
*/
struct llist *create_llist()
//@ requires true;
//@ ensures llist(result, nil);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  //@ close nodes(n, nil);
  //@ close llist(l, nil);
  return l;
}


/***
 * Description:
The list_add function adds an element to the end of the linked list,

@param list: a single linked list
@param x: the element to be added

It makes sure that the list has added x as its last element.
*/
void llist_add(struct llist *list, int x)
//@ requires llist(list, ?vs);
//@ ensures llist(list, append(vs, cons(x, nil)));
{
  //@ open llist(list, vs);
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  l = list->last;
  l->next = n;
  l->value = x;
  list->last = n;
  //@ open nodes(list->first, vs);
  //@ if (list->first == l) {
  //@   close nodes(n, nil);
  //@   close nodes(list->first, cons(x, nil));
  //@ } else {
  //@   struct node *first = list->first;
  //@   assert first->next |-> ?next;
  //@   assert first->value |-> ?v;
  //@   assert nodes(next, ?tail_values);
  //@   assert vs == cons(v, tail_values);
  //@   if (next == l) {
  //@     close nodes(n, nil);
  //@     close nodes(l, cons(x, nil));
  //@     close nodes(first, cons(v, cons(x, nil)));
  //@   } else {
  //@     // Inductive case for longer lists
  //@     assert next != 0;
  //@     assert next != l;
  //@     assert nodes(next, tail_values);
  //@     // Helper lemma to update the last node in the list
  //@     nodes_append_last(next, tail_values, l, x);
  //@     close nodes(first, cons(v, append(tail_values, cons(x, nil))));
  //@     append_cons(v, tail_values, cons(x, nil));
  //@   }
  //@ }
  //@ close llist(list, append(vs, cons(x, nil)));
}

/*@
// Helper lemma to update the last node in a list
lemma void nodes_append_last(struct node *node, list<int> values, struct node *last, int x)
  requires nodes(node, values) &*& last != 0 &*& last->next |-> ?n &*& last->value |-> _ &*& malloc_block_node(last);
  ensures nodes(node, append(values, cons(x, nil))) &*& last->value |-> x &*& last->next |-> n;
{
  open nodes(node, values);
  if (node == last) {
    close nodes(n, nil);
    close nodes(node, cons(x, nil));
  } else {
    nodes_append_last(node->next, tail(values), last, x);
    close nodes(node, append(values, cons(x, nil)));
  }
}

// Helper lemma for append with cons
lemma void append_cons<t>(t x, list<t> xs, list<t> ys)
  requires true;
  ensures append(cons(x, xs), ys) == cons(x, append(xs, ys));
{
}
@*/

/***
 * Description:
The llist_append function appends the second list to the end of the first list,

@param list1: a single linked list to which another list is appended
@param list2: a single linked list to be appended to the end of list1

It makes sure that list2 is appended to the end of list1.
*/
void llist_append(struct llist *list1, struct llist *list2)
//@ requires llist(list1, ?vs1) &*& llist(list2, ?vs2);
//@ ensures llist(list1, append(vs1, vs2));
{
  //@ open llist(list1, vs1);
  //@ open llist(list2, vs2);
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  if (f2 == l2) {
    //@ open nodes(f2, vs2);
    //@ assert vs2 == nil;
    free(l2);
    free(list2);
    //@ close nodes(list1->first, vs1);
    //@ close llist(list1, vs1);
  } else {
    //@ open nodes(f2, vs2);
    //@ assert f2->next |-> ?next_f2;
    //@ assert f2->value |-> ?v_f2;
    //@ assert nodes(next_f2, ?tail_vs2);
    //@ assert vs2 == cons(v_f2, tail_vs2);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    free(f2);
    free(list2);
    //@ nodes_append(list1->first, vs1, next_f2, tail_vs2);
    //@ close llist(list1, append(vs1, vs2));
  }
}

/*@
// Helper lemma to append two node lists
lemma void nodes_append(struct node *node1, list<int> values1, struct node *node2, list<int> values2)
  requires nodes(node1, values1) &*& nodes(node2, values2) &*& node1 != 0;
  ensures nodes(node1, append(values1, values2));
{
  open nodes(node1, values1);
  if (values1 == nil) {
    assert node1->next |-> 0;
    node1->next = node2;
    close nodes(node1, values2);
  } else {
    assert node1->next |-> ?next;
    assert node1->value |-> ?v;
    assert nodes(next, ?tail_values1);
    if (next == 0) {
      node1->next = node2;
      close nodes(node1, cons(v, values2));
    } else {
      nodes_append(next, tail_values1, node2, values2);
      close nodes(node1, cons(v, append(tail_values1, values2)));
      append_cons(v, tail_values1, values2);
    }
  }
}
@*/

/***
 * Description:
The llist_dispose function frees a list by iteratively freeing the nodes.

@param list: a single linked list to be freed
*/
void llist_dispose(struct llist *list)
//@ requires llist(list, ?vs);
//@ ensures true;
{
  //@ open llist(list, vs);
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
  //@ invariant nodes(n, ?remaining) &*& n != 0;
  {
    //@ open nodes(n, remaining);
    struct node *next = n->next;
    free(n);
    n = next;
    //@ assert nodes(n, ?new_remaining);
  }
  //@ open nodes(l, ?last_values);
  free(l);
  free(list);
}


/***
 * Description:
The llist_length_iterative function iteratively calculates the length of the linked list,
which is the number of nodes from first (inclusive) to last (exclusive).
For example, if first = last, then the length is 0; If first's next = last, then the length is 1.

@param list: a single linked list

It makes sure that the list is not changed, and the return value is the length of the list.
*/
int llist_length_iterative(struct llist *list)
//@ requires llist(list, ?vs);
//@ ensures llist(list, vs) &*& result == length(vs);
{
  //@ open llist(list, vs);
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  //@ assert nodes(f, vs);
  //@ nodes_to_length(f, vs, l);
  while (n != l)
  //@ invariant nodes_length(f, vs, n, c, l);
  {
    //@ open nodes_length(f, vs, n, c, l);
    //@ open nodes_until(n, ?ns, l);
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
    //@ close nodes_length(f, vs, n, c, l);
  }
  //@ open nodes_length(f, vs, l, c, l);
  //@ close llist(list, vs);
  return c;
}

/*@
// Helper predicate to track length during iteration
predicate nodes_length(struct node *first, list<int> values, struct node *current, int count, struct node *last) =
  nodes(first, values) &*& nodes_until(first, ?nodes_to_current, current) &*& 
  count == length(nodes_to_current) &*& current != 0 &*& last != 0;

// Helper predicate to track nodes until a specific node
predicate nodes_until(struct node *from, list<struct node *> nodes, struct node *to) =
  from == to ?
    nodes == nil
  :
    from != 0 &*& from->next |-> ?next &*& nodes_until(next, ?rest, to) &*& 
    nodes == cons(from, rest);

// Helper lemma to convert nodes to length tracking
lemma void nodes_to_length(struct node *first, list<int> values, struct node *last)
  requires nodes(first, values) &*& first != 0 &*& last != 0;
  ensures nodes_length(first, values, first, 0, last);
{
  close nodes_until(first, nil, first);
  close nodes_length(first, values, first, 0, last);
}
@*/

/***
 * Description:
The llist_length_recursive_helper function recursively calculates the length of the list segment between n1 and n2.
For example, if n1 = n2, then the length is 0. If n1->n->n2, then the length is calculated recursively as 2.

@param n1: the node at the beginning of the list segment
@param n2: the node at the end of the list segment

It make sures that the list segment is not changed, and the return value is the length of such list segment.
*/
int llist_length_recursive_helper(struct node *n1, struct node *n2)
//@ requires lseg(n1, n2, ?vs);
//@ ensures lseg(n1, n2, vs) &*& result == length(vs);
{
  //@ open lseg(n1, n2, vs);
  int len;
  if(n1 == n2) {
    len = 0;
    //@ close lseg(n1, n2, nil);
  } else {
    len = llist_length_recursive_helper(n1->next, n2);
    len = len + 1;
    //@ close lseg(n1, n2, vs);
  }
  return len;
}

/*@
// Helper predicate for list segments
predicate lseg(struct node *from, struct node *to, list<int> values) =
  from == to ?
    values == nil
  :
    from != 0 &*& from->value |-> ?v &*& from->next |-> ?next &*& malloc_block_node(from) &*&
    lseg(next, to, ?tail_values) &*& values == cons(v, tail_values);
@*/

/***
 * Description:
The llist_length_recursive function recursively calculates the length of the linked list.

@param l: a single linked list

It makes sure that the list is not changed, and the return value is the length of the list.
*/
int llist_length_recursive(struct llist *l)
//@ requires llist(l, ?vs);
//@ ensures llist(l, vs) &*& result == length(vs);
{
  //@ open llist(l, vs);
  //@ nodes_to_lseg(l->first, l->last, vs);
  int result = llist_length_recursive_helper(l->first, l->last);
  //@ lseg_to_nodes(l->first, l->last, vs);
  //@ close llist(l, vs);
  return result;
}

/*@
// Helper lemma to convert nodes to lseg
lemma void nodes_to_lseg(struct node *first, struct node *last, list<int> values)
  requires nodes(first, values) &*& last != 0;
  ensures lseg(first, last, values);
{
  open nodes(first, values);
  if (first == 0) {
    close lseg(first, last, nil);
  } else if (first == last) {
    close lseg(first, last, nil);
  } else {
    assert first->next |-> ?next;
    assert first->value |-> ?v;
    assert nodes(next, ?tail_values);
    nodes_to_lseg(next, last, tail_values);
    close lseg(first, last, values);
  }
}

// Helper lemma to convert lseg back to nodes
lemma void lseg_to_nodes(struct node *first, struct node *last, list<int> values)
  requires lseg(first, last, values) &*& last != 0;
  ensures nodes(first, values);
{
  open lseg(first, last, values);
  if (first == last) {
    close nodes(first, nil);
  } else {
    assert first->next |-> ?next;
    assert first->value |-> ?v;
    assert lseg(next, last, ?tail_values);
    lseg_to_nodes(next, last, tail_values);