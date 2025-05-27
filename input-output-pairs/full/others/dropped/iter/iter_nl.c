#include "stdlib.h"

/***
 * Struct: node
 * Description:
 * Represents a single node in a linked list.
 * Each node stores an integer value and a pointer to the next node.
 */
struct node {
  struct node *next;
  int value;
};

/***
 * Struct: llist
 * Description:
 * Represents a singly linked list, tracking both the first and last node.
 * The list always ends with a dummy tail node.
 */
struct llist {
  struct node *first;
  struct node *last;
};

/***
 * Function: create_llist
 * Description:
 * Initializes an empty linked list.
 * Allocates both the list structure and an initial dummy node, which acts as the tail.
@return Pointer to the newly created list.
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
 * Function: llist_add
 * Description:
 * Adds a new element with the given value to the end of the list.
 * Maintains a dummy tail node by allocating a new one during each addition.
@param list - the list to which the value will be added.
@param x - the value to insert.
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
 * Function: llist_append
 * Description:
 * Appends the contents of `list2` to `list1`.
 * Merges the two lists and disposes of the redundant dummy node and list2 object.
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
 * Function: llist_dispose
 * Description:
 * Frees all memory allocated for the list, including all nodes and the list structure itself.
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
 * Function: llist_length
 * Description:
 * Calculates the number of elements in the list (excluding the dummy node).
@return Number of real elements.
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
 * Function: llist_lookup
 * Description:
 * Retrieves the value at the given index in the list.
@param index - zero-based index into the list.
@return The integer value at the specified position.
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
 * Function: llist_removeFirst
 * Description:
 * Removes and returns the first element in the list.
 * Updates the head pointer to the next node.
@return The value of the removed element.
 */
int llist_removeFirst(struct llist *l)
{
  struct node *nf = l->first;
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  return nfv;
}

/***
 * Function: main0
 * Description:
 * Demonstrates remove elements in list.
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
 * Function: main
 * Description:
 * Demonstrates creation, addition, lookup, and appending of two lists.
 * Verifies correctness through assertions and disposes memory at the end.
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

/***
 * Struct: iter
 * Description:
 * Represents an iterator over a linked list.
 * Keeps track of the current node during traversal.
 */
struct iter {
    struct node *current;
};

/***
 * Function: llist_create_iter
 * Description:
 * Creates a new iterator for the given list.
 * The iterator starts at the beginning of the list.
@return Pointer to the new iterator.
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
 * Function: iter_next
 * Description:
 * Advances the iterator by one node and returns the current node's value.
@return The value at the current iterator position.
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
 * Function: iter_dispose
 * Description:
 * Frees the memory allocated for the iterator object.
 */
void iter_dispose(struct iter *i)
{
    free(i);
}

/***
 * Function: main2
 * Description:
 * Demonstrates usage of iterators.
 * Creates two independent iterators over the same list and verifies their behavior.
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
