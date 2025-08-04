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
// A predicate to represent the state of a cell.
// It holds the value 'v' stored in the cell 'c'.
predicate cell(struct cell *c; int v) = c->val |-> v;

// A predicate family to abstract over the data required by different
// implementations of the 'equals' function type.
// It is indexed by the function pointer 'f' and takes the data pointer 'p'.
predicate_family eq_data(void* f)(void* p);
@*/


/*equals() function
-params: void* x1, void* x2
-description: checks whether the elements of two pointers are equal. It doesn't have a concrete definition.
*/
typedef bool equals(void* x1, void* x2);
//@ requires eq_data(this)(x1) &*& eq_data(this)(x2);
//@ ensures eq_data(this)(x1) &*& eq_data(this)(x2);

/*@
// An instance of the eq_data predicate family for the cell_equals function.
// It specifies that the required data for a pointer 'p' is the 'cell' predicate.
// The pointer 'p' is cast to 'struct cell*' to be used with the 'cell' predicate.
predicate_family_instance eq_data(cell_equals)(void* p) = cell((struct cell*)p, _);
@*/

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
  
  return x1->val == x2->val;

}