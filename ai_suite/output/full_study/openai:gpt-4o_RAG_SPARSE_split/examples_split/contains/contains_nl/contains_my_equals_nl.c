#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};

/*equals() function
-params: void* v1, void* v2
-description: checks whether two pointers are equal. It doesn't have a concrete definition.
*/
typedef bool equals(void* v1, void* v2);

//@ predicate equals_predicate(void* v1, void* v2) = true;

// TODO: make this function pass the verification
/*my_equals() function
-params: void* v1, void* v2
-description: checks whether two pointers have an equal value.
*/
bool my_equals(void* v1, void* v2) //@: equals
    //@ requires equals_predicate(v1, v2);
    //@ ensures equals_predicate(v1, v2) &*& result == ((uintptr_t)v1 == (uintptr_t)v2);
{
  if((uintptr_t)v1 == (uintptr_t)v2) {
    return true;
  } else {
    return false;
  }
}