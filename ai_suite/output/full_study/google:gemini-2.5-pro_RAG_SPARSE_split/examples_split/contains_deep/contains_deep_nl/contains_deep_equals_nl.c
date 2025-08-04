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
// A predicate family to abstractly represent the data pointed to by a void pointer.
// It is parameterized by the 'equals' function pointer 'p' to allow for different
// implementations of 'equals' to work on different data types.
// We assume the abstract value of the data can be represented as an integer,
// which is a reasonable assumption given the 'struct cell' definition.
predicate_family eq_pred(void *p)(void *data, int value);
@*/

// TODO: make this function pass the verification
/*equals() function
-params: void* x1, void* x2
-description: checks whether the elements of two pointers are equal. It doesn't have a concrete definition.
*/
typedef bool equals(void* x1, void* x2);
    /*@ requires eq_pred(this)(x1, ?v1) &*& eq_pred(this)(x2, ?v2);
        ensures  eq_pred(this)(x1, v1) &*& eq_pred(this)(x2, v2) &*& result == (v1 == v2);
    @*/