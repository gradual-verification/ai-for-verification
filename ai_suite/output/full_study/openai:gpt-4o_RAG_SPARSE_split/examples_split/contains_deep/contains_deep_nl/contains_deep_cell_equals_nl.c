#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};

// specific to cell

struct cell {
  int val;
};

/*equals() function
-params: void* x1, void* x2
-description: checks whether the elements of two pointers are equal. It doesn't have a concrete definition.
*/
typedef bool equals(void* x1, void* x2);

//@ predicate cell(struct cell* c; int v) = c->val |-> v &*& malloc_block_cell(c);

// TODO: make this function pass the verification
/*cell_equals() function
-params: two cell pointers
-description: compares the values of the two cells.
It ensures that the two cells are unchanged, and the return value is true if the values are equal, false otherwise.
*/
bool cell_equals(struct cell* x1, struct cell* x2) //@: equals
  //@ requires cell(x1, ?v1) &*& cell(x2, ?v2);
  //@ ensures cell(x1, v1) &*& cell(x2, v2) &*& result == (v1 == v2);
{
  //@ open cell(x1, v1);
  //@ open cell(x2, v2);
  bool result = x1->val == x2->val;
  //@ close cell(x1, v1);
  //@ close cell(x2, v2);
  return result;
}