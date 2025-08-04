#include "stdlib.h"
#include "assert.h"
#include "limits.h"
//@ #include "list.gh"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

/*@
predicate lseg(struct node *from, struct node *to, list<int> vs) =
    from == to ?
        vs == nil
    :
        from != 0 &*&
        from->next |-> ?next &*&
        from->value |-> ?v &*&
        malloc_block_node(from) &*&
        lseg(next, to, ?rest) &*&
        vs == cons(v, rest);

predicate llist(struct llist *l, list<int> vs) =
    l->first |-> ?f &*&
    l->last |-> ?t &*&
    malloc_block_llist(l) &*&
    lseg(f, t, vs) &*&
    t != 0 &*&
    t->next |-> 0 &*&
    t->value |-> _ &*&
    malloc_block_node(t);

lemma void lseg_append_node(struct node *from, struct node *to)
    requires lseg(from, to, ?vs) &*& to->value |-> ?v &*& to->next |-> ?next &*& malloc_block_node(to);
    ensures lseg(from, next, append(vs, cons(v, nil)));
{
    open lseg(from, to, vs);
    if (from == to) {
        close lseg(next, next, nil);
        close lseg(from, next, cons(v, nil));
    } else {
        lseg_append_node(from->next, to);
        close lseg(from, next, append(vs, cons(v, nil)));
    }
}

lemma void lseg_append(struct node *from, struct node *mid, struct node *to)
    requires lseg(from, mid, ?vs1) &*& lseg(mid, to, ?vs2);
    ensures lseg(from, to, append(vs1, vs2));
{
    open lseg(from, mid, vs1);
    if (from == mid) {
    } else {
        lseg_append(from->next, mid, to);
        close lseg(from, to, append(vs1, vs2));
    }
}
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
  //@ close lseg(n, n, nil);
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
  //@ assert list->first |-> ?f;
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  l = list->last;
  l->next = n;
  l->value = x;
  list->last = n;
  //@ lseg_append_node(f, l);
  //@ close llist(list, append(vs, cons(x, nil)));
}


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
  //@ assert list1->first |-> ?f1;
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  if (f2 == l2) {
    //@ open lseg(f2, l2, vs2);
    free(l2);
    free(list2);
    //@ append_nil(vs1);
    //@ close llist(list1, vs1);
  } else {
    //@ open lseg(f2, l2, vs2);
    //@ assert f2->value |-> ?v2_head &*& f2->next |-> ?f2_next;
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    free(f2);
    free(list2);
    //@ lseg_append_node(f1, l1);
    //@ lseg_append(f1, f2_next, l2);
    //@ append_assoc(vs1, cons(v2_head, nil), tail(vs2));
    //@ close llist(list1, append(vs1, vs2));
  }
}


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
    //@ invariant lseg(n, l, _);
  {
    //@ open lseg(n, l, _);
    struct node *next = n->next;
    free(n);
    n = next;
  }
  //@ open lseg(l, l, _);
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
  //@ close lseg(f, f, nil);
  while (n != l)
    /*@ invariant lseg(f, n, ?pfx) &*& lseg(n, l, ?sfx) &*& vs == append(pfx, sfx) &*&
                  c == length(pfx) &*& c <= INT_MAX;
    @*/
  {
    //@ open lseg(n, l, sfx);
    struct node *next = n->next;
    //@ lseg_append_node(f, n);
    //@ append_assoc(pfx, cons(head(sfx), nil), tail(sfx));
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
  }
  //@ open lseg(l, l, _);
  //@ lseg_append(f, l, l);
  //@ append_nil(vs);
  //@ close llist(list, vs);
  return c;
}


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
  } else {
    len = llist_length_recursive_helper(n1->next, n2);
    len = len + 1;
  }
  //@ close lseg(n1, n2, vs);
  return len;
}


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
  int result = llist_length_recursive_helper(l->first, l->last);
  //@ close llist(l, vs);
  return result;
}


/***
 * Description:
The `llist_lookup` function looks up the value at the given index in the linked list.
Note that the index in the linked list starts at 0.

@param list - Pointer to the linked list structure.
@param index - The index of the value to be looked up, which is within the range of the linked list.
@return - The value at the given index in the linked list.

It makes sure that the list is not changed, and the return value is the value at the given index in the list.
*/
int llist_lookup(struct llist *list, int index)
    //@ requires llist(list, ?vs) &*& 0 <= index &*& index < length(vs);
    //@ ensures llist(list, vs) &*& result == nth(index, vs);
{
  //@ open llist(list, vs);
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  //@ close lseg(f, f, nil);
  while (i < index)
    /*@ invariant lseg(f, n, ?pfx) &*& lseg(n, l, ?sfx) &*& vs == append(pfx, sfx) &*&
                  i == length(pfx) &*& i <= index;
    @*/
  {
    //@ open lseg(n, l, sfx);
    struct node *next = n->next;
    //@ lseg_append_node(f, n);
    //@ append_assoc(pfx, cons(head(sfx), nil), tail(sfx));
    n = next;
    i = i + 1;
  }
  //@ open lseg(n, l, sfx);
  int value = n->value;
  //@ assert head(sfx) == value;
  //@ append_take_drop_n(vs, index);
  //@ assert sfx == drop(index, vs);
  //@ assert nth(index, vs) == head(drop(index, vs));
  //@ close lseg(n, l, sfx);
  //@ lseg_append(f, n, l);
  //@ close llist(list, vs);
  return value;
}


/***
 * Description:
The `llist_removeFirst` function removes the first node from the non-empty linked list and returns its value.

@param l - Pointer to the non-empty linked list structure.
@return - The value of the first node that is removed from the linked list.
*/
int llist_removeFirst(struct llist *l)
    //@ requires llist(l, ?vs) &*& vs != nil;
    //@ ensures llist(l, tail(vs)) &*& result == head(vs);
{
  //@ open llist(l, vs);
  struct node *nf = l->first;
  //@ open lseg(nf, l->last, vs);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ close llist(l, tail(vs));
  return nfv;
}


/***
 * Description:
The `main` function tests the functions of llist by creating two linked lists,
adding elements to them, removing the element, appending them together,
looking up the element at each position, and then disposing of the list.
*/
int main() //@ : main
{
  struct llist *l1 = create_llist();
  struct llist *l2 = create_llist();
  llist_add(l1, 10);
  llist_add(l1, 20);
  llist_add(l1, 30);
  llist_add(l2, 40);
  llist_add(l2, 50);
  llist_add(l2, 60);
  int x = llist_removeFirst(l2);
  assert(x == 40);
  llist_append(l1, l2);
  int n1 = llist_length_iterative(l1);
  assert(n1 == 5);
  int n2 = llist_length_recursive(l1);
  assert(n2 == 5);
  int e0 = llist_lookup(l1, 0);
  assert(e0 == 10);
  int e1 = llist_lookup(l1, 1);
  assert(e1 == 20);
  int e2 = llist_lookup(l1, 2);
  assert(e2 == 30);
  int e3 = llist_lookup(l1, 3);
  assert(e3 == 50);
  int e4 = llist_lookup(l1, 4);
  assert(e4 == 60);
  llist_dispose(l1);
  return 0;
}