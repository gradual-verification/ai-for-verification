#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};

// specific to cell

struct cell {
  int val;
};

/*@
predicate cell(struct cell *c; int v) =
  c->val |-> v &*& malloc_block_cell(c);
@*/

// TODO: make this function pass the verification
/*create_cell() function
-params: an integer
-description: creates a cell with the given value*/
struct cell* create_cell(int v)
  //@ requires true;
  //@ ensures cell(result, v);
{
  struct cell* c = malloc(sizeof(struct cell));
  if(c == 0) abort();
  c->val = v;
  return c;
}