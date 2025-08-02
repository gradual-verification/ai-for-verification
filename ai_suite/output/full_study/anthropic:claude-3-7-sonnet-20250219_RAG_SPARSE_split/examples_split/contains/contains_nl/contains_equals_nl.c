#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};


// TODO: make this function pass the verification
/*equals() function
-params: void* v1, void* v2
-description: checks whether two pointers are equal. It doesn't have a concrete definition.
*/
/*@
// Define a predicate for the equals function
predicate_family equals_pre(void *equals_func)(void *v1, void *v2);
predicate_family equals_post(void *equals_func)(void *v1, void *v2, bool result);
@*/

typedef bool equals(void* v1, void* v2);
//@ requires equals_pre(this)(v1, v2);
//@ ensures equals_post(this)(v1, v2, result);

/*@
// Define a specific instance for our equals function
predicate_family_instance equals_pre(pointer_equals)(void *v1, void *v2) = 
    pointer_within_limits(v1) == true &*& pointer_within_limits(v2) == true;

predicate_family_instance equals_post(pointer_equals)(void *v1, void *v2, bool result) = 
    pointer_within_limits(v1) == true &*& pointer_within_limits(v2) == true &*& result == ((uintptr_t)v1 == (uintptr_t)v2);
@*/

bool pointer_equals(void* v1, void* v2) //@ : equals
//@ requires equals_pre(pointer_equals)(v1, v2);
//@ ensures equals_post(pointer_equals)(v1, v2, result);
{
    //@ open equals_pre(pointer_equals)(v1, v2);
    bool result = (v1 == v2);
    //@ close equals_post(pointer_equals)(v1, v2, result);
    return result;
}