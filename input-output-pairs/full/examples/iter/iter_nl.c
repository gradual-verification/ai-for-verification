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
The create_llist function allocates an empty linked list with a node as both the first and last of the linked list.

It makes sure that the return value is an empty list. 
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
The list_add function adds an element to the end of the linked list,

@param list: a single linked list
@param x: the element to be added

It makes sure that the list has added x as its last element.
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
The llist_dispose function frees a list by iteratively freeing the nodes.

@param list: a single linked list to be freed
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
The `main` function tests the functions of llist by creating a linked list,
adding elements to it, creating 2 iterators and iterating over the linked list,
and finally disposing of the iterators and the list.
*/
int main()
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