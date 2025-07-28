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


/***
 * Description:
The llist_length_iterative function iteratively calculates the length of the linked list,
which is the number of nodes from first (inclusive) to last (exclusive).
For example, if first = last, then the length is 0; If first's next = last, then the length is 1.

@param list: a single linked list

It makes sure that the list is not changed, and the return value is the length of the list.
*/
int llist_length_iterative(struct llist *list)
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
The llist_append function appends the second list to the end of the first list,

@param list1: a single linked list to which another list is appended
@param list2: a single linked list to be appended to the end of list1

It makes sure that list2 is appended to the end of list1.
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
The `llist_removeFirst` function removes the first node from the non-empty linked list and returns its value.

@param l - Pointer to the non-empty linked list structure.
@return - The value of the first node that is removed from the linked list.
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
The llist_length_recursive function recursively calculates the length of the linked list.

@param l: a single linked list

It makes sure that the list is not changed, and the return value is the length of the list.
*/
int llist_length_recursive(struct llist *l)
{
  return llist_length_recursive_helper(l->first, l->last);
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


// TODO: make this function pass the verification
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
  int x = llist_removeFirst(l2); assert(x == 40);
  llist_append(l1, l2);
  int n1 = llist_length_iterative(l1); assert(n1 == 5);
  int n2 = llist_length_recursive(l1); assert(n2 == 5);
  int e0 = llist_lookup(l1, 0); assert(e0 == 10);
  int e1 = llist_lookup(l1, 1); assert(e1 == 20);
  int e2 = llist_lookup(l1, 2); assert(e2 == 30);
  int e3 = llist_lookup(l1, 3); assert(e3 == 50);
  int e4 = llist_lookup(l1, 4); assert(e4 == 60);
  llist_dispose(l1);
  return 0;
}