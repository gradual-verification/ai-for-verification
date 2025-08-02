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


/*cell_equals() function
-params: two cell pointers
-description: compares the values of the two cells.
It ensures that the two cells are unchanged, and the return value is true if the values are equal, false otherwise.
*/
/*@
  predicate cell(struct cell* c; int value) = 
    c->val |-> value &*& malloc_block_cell(c);
    
  predicate_family equals_pre(void* equals_func)(void* x1, void* x2);
  predicate_family equals_post(void* equals_func)(void* x1, void* x2, bool result);
  
  predicate_family_instance equals_pre(cell_equals)(void* x1, void* x2) =
    cell((struct cell*)x1, ?v1) &*& cell((struct cell*)x2, ?v2);
    
  predicate_family_instance equals_post(cell_equals)(void* x1, void* x2, bool result) =
    cell((struct cell*)x1, ?v1) &*& cell((struct cell*)x2, ?v2) &*& result == (v1 == v2);
@*/

bool cell_equals(struct cell* x1, struct cell* x2) //@ : equals
//@ requires equals_pre(cell_equals)(x1, x2);
//@ ensures equals_post(cell_equals)(x1, x2, result);
{
  //@ open equals_pre(cell_equals)(x1, x2);
  //@ open cell(x1, ?v1);
  //@ open cell(x2, ?v2);
  
  bool result = x1->val == x2->val;
  
  //@ close cell(x1, v1);
  //@ close cell(x2, v2);
  //@ close equals_post(cell_equals)(x1, x2, result);
  return result;
}