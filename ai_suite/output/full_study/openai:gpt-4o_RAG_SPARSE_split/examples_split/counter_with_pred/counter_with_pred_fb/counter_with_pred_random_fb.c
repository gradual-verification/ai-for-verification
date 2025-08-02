#include "stdlib.h"

struct Counter {
  int value;
};

/*@
predicate Counter(struct Counter* c, int v) =
  c->value |-> v;
@*/

// TODO: make this function pass the verification
bool random();
//@ requires true;
//@ ensures true;

bool random() {
    // This function is intended to simulate a random boolean value.
    // Since we don't have a specific implementation, we assume it can return either true or false.
    return true; // or return false;
}