#include "stdlib.h"

struct Counter {
  int value;
};

// TODO: make this function pass the verification
/***
 * Description:
The random function generates a random boolean value.

The function does not modify the state of any variables, and we don't need to implement it.
*/
//@ predicate random_predicate() = true;

bool random();
//@ requires random_predicate();
//@ ensures random_predicate() &*& (result == true || result == false);
