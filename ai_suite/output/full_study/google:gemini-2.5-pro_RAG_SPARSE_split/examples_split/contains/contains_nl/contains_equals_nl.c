#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};

/*@

// A predicate family to associate a value pointer with its abstract representation.
// The equality function pointer `p` is used as an index to distinguish
// different equality functions and their corresponding value representations.
// The representation is a list of characters, which is a generic way to model any data.
predicate_family eq_value_inv(void *p)(void *v, list<char> repr);

@*/

// TODO: make this function pass the verification
/*equals() function
-params: void* v1, void* v2
-description: checks whether two pointers are equal. It doesn't have a concrete definition.
*/
typedef bool equals(void* v1, void* v2);
/*@
    requires
        // The caller must provide the resources for both values,
        // along with their abstract representations `r1` and `r2`.
        // `this` refers to the function pointer being called.
        eq_value_inv(this)(v1, ?r1) &*&
        eq_value_inv(this)(v2, ?r2);
    ensures
        // The function must preserve the resources for both values.
        eq_value_inv(this)(v1, r1) &*&
        eq_value_inv(this)(v2, r2) &*&
        // The result of the function must correspond to the equality
        // of the abstract representations.
        result == (r1 == r2);
@*/