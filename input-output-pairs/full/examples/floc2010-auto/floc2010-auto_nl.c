#include "stdlib.h"

struct node {
  int value;
  struct node *next;
};

/***
 * Description:
The create_node function allocates a node with the specified fields of value and next.

@param value: the specified value for the field value in the new node
@param next: the specified next for the field next in the new node
*/
struct node *create_node(int value, struct node *next)
{
  struct node *n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->value = value;
  n->next = next;
  return n;
}

struct list {
  struct node *first;
  struct node *last;
};

/***
 * Description:
The create_node function allocates an empty linked list with a node as both the first and last of the linked list.
*/
struct list *create_list()
{
  struct list *l = malloc(sizeof(struct list));
  if(l == 0) abort();
  struct node* n = create_node(0, 0);
  l->first = n;
  l->last = n;
  return l;
}

/***
 * Description:
The list_length_helper function calculates the length of the list segment between n1 and n2.
For example, if n1 = n2, then the length is 0. If n1->n->n2, then the length is calculated recursively as 2.

@param n1: the node at the beginning of the list segment
@param n2: the node at the end of the list segment
*/
int list_length_helper(struct node *n1, struct node *n2)
{
  int len;
  if(n1 == n2) {
    len = 0;
  } else {
    len = list_length_helper(n1->next, n2);
    len = len + 1;
  }
  return len;
}

/***
 * Description:
The list_length function calculates the length of the linked list.

@param l: a single linked list
*/
int list_length(struct list *l)
{
  return list_length_helper(l->first, l->last);
}

/***
 * Description:
The list_add function adds an element to the end of the linked list,
by allocating a new node, assigning its value and making it as the last node of the linked list.

@param l: a single linked list
@param x: the element to be added
*/
void list_add(struct list *l, int x)
{
  struct node *n = create_node(0, 0);
  struct node *nl = l->last;
  nl->next = n;
  nl->value = x;
  l->last = n;
}