#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

/***
 * Description:
The `create_llist` function dynamically allocates memory for a linked list structure
and initializes it with an empty node (where first = last).

@return - Pointer to the newly created linked list structure.
*/
struct llist *create_llist()
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  return l;
}

/***
 * Description:
The `llist_add` function adds a new node with the given value to the end of the linked list.
Note that the original last node contains the added value, and a new last node is created.

@param list - Pointer to the linked list structure.
@param x - Value to be added to the linked list.
*/
void llist_add(struct llist *list, int x)
{
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  l = list->last;
  l->next = n;
  l->value = x;
  list->last = n;
}

/***
 * Description:
The `llist_append` function appends the second linked list to the end of the first linked list.
Note that the original last node of the first linked list becomes the first node of the second linked list,
by doing some assignments on next and value.

@param list1 - Pointer to the first linked list structure.
@param list2 - Pointer to the second linked list structure.
*/
void llist_append(struct llist *list1, struct llist *list2)
{
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  if (f2 == l2) {
    free(l2);
    free(list2);
  } else {
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    free(f2);
    free(list2);
  }
}

/***
 * Description:
The `llist_dispose` function frees the memory occupied by all nodes in the linked list and the linked list itself.

@param list - Pointer to the linked list structure.
*/
void llist_dispose(struct llist *list)
{
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
  {
    struct node *next = n->next;
    free(n);
    n = next;
  }
  free(l);
  free(list);
}

/***
 * Description:
The `llist_length` function calculates the length of the linked list, 
which is the number of nodes from first (inclusive) to last (exclusive).
For example, if first = last, then the length is 0; If first's next = last, then the length is 1.

@param list - Pointer to the linked list structure.
@return - The length of the linked list.
*/
int llist_length(struct llist *list)
{
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  while (n != l)
  {
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
  }
  return c;
}

/***
 * Description:
The `llist_lookup` function looks up the value at the given index in the linked list.
Note that the index in the linked list starts at 0.

@param list - Pointer to the linked list structure.
@param index - The index of the value to be looked up, which is within the range of the linked list.
@return - The value at the given index in the linked list.
*/
int llist_lookup(struct llist *list, int index)
{
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  while (i < index)
  {
    struct node *next = n->next;
    n = next;
    i = i + 1;
  }
  int value = n->value;
  return value;
}

/***
 * Description:
The `llist_removeFirst` function removes the first node from the non-empty linked list and returns its value.

@param l - Pointer to the non-empty linked list structure.
@return - The value of the first node that is removed from the linked list.
*/
int llist_removeFirst(struct llist *l)
{
  struct node *nf = l->first;
  //@ open lseg(nf, ?nl, v);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  return nfv;
}

/***
 * Description:
The `main0` function tests the `llist_add` and `llist_removeFirst` functions by creating a linked list,
adding elements to it, removing the first two elements, and then disposing of the list.
It asserts that the removed elements have the correct values.
*/
void main0()
{
  struct llist *l = create_llist();
  llist_add(l, 10);
  llist_add(l, 20);
  llist_add(l, 30);
  llist_add(l, 40);
  int x1 = llist_removeFirst(l);
  assert(x1 == 10);
  int x2 = llist_removeFirst(l);
  assert(x2 == 20);
  llist_dispose(l);
}

/***
 * Description:
The `main` function tests the functions of llist by creating two linked lists,
adding elements to them, removing the element, appending them together,
looking up the element at each position, and then disposing of the list.
*/
int main() 
{
  struct llist *l1 = create_llist();
  struct llist *l2 = create_llist();
  llist_add(l1, 10);
  llist_add(l1, 20);
  llist_add(l1, 30);
  llist_add(l2, 40);
  llist_add(l2, 50);
  llist_add(l2, 60);
  int x = llist_removeFirst(l2); assert(x == 40);
  llist_append(l1, l2);
  int n = llist_length(l1); assert(n == 5);
  int e0 = llist_lookup(l1, 0); assert(e0 == 10);
  int e1 = llist_lookup(l1, 1); assert(e1 == 20);
  int e2 = llist_lookup(l1, 2); assert(e2 == 30);
  int e3 = llist_lookup(l1, 3); assert(e3 == 50);
  int e4 = llist_lookup(l1, 4); assert(e4 == 60);
  llist_dispose(l1);
  return 0;
}

struct iter {
    struct node *current;
};

/**
 * Description:
The `llist_create_iter` function creates an iterator for a given linked list,
which is located at the first node of the linked list.
Note that the linked list cannot be modified unless we free the iterator.

@param l - Pointer to the linked list structure.
@return - The created iterator pointing to the first node of linked list.
*/
struct iter *llist_create_iter(struct llist *l)
{
    struct iter *i = 0;
    struct node *f = 0;
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }
    f = l->first;
    i->current = f;
    return i;
}

/***
 * Description:
The `iter_next` function returns the value of the current node of the iterator
and moves the iterator to the next node. It requires that the iterator is not at the end of the linked list.
Note that the linked list cannot be modified unless we free the iterator.

@param i - Iterator of the linked list.
@return - The value of the original node that the iterator is at.
*/
int iter_next(struct iter *i)
{
    struct node *c = i->current;
    int value = c->value;
    struct node *n = c->next;
    i->current = n;
    return value;
}

/***
 * Description:
The `iter_dispose` function deallocates the memory associated with the iterator.

@param i - Iterator of the linked list
*/
void iter_dispose(struct iter *i)
{
    free(i);
}

/***
 * Description:
The `main2` function tests the functions of llist by creating a linked list,
adding elements to it, creating 2 iterators and iterating over the linked list,
and finally disposing of the iterators and the list.
*/
int main2()
{
    struct llist *l = create_llist();
    llist_add(l, 5);
    llist_add(l, 10);
    llist_add(l, 15);
    struct iter *i1 = llist_create_iter(l);
    struct iter *i2 = llist_create_iter(l);
    int i1e1 = iter_next(i1); assert(i1e1 == 5);
    int i2e1 = iter_next(i2); assert(i2e1 == 5);
    int i1e2 = iter_next(i1); assert(i1e2 == 10);
    int i2e2 = iter_next(i2); assert(i2e2 == 10);
    iter_dispose(i1);
    iter_dispose(i2);
    llist_dispose(l);
    return 0;
}
