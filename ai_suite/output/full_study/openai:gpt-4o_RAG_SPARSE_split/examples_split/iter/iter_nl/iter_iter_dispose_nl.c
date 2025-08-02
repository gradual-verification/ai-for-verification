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

// TODO: make this function pass the verification
/***
 * Description:
The `iter_dispose` function deallocates the memory associated with the iterator.

@param i - Iterator of the linked list
*/
//@ requires i != 0 &*& malloc_block_iter(i);
//@ ensures emp;
void iter_dispose(struct iter *i)
{
    free(i);
}