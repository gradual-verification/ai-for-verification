#include "stdlib.h"

struct Counter {
  int value;
};

/*@
predicate Counter(struct Counter* c, int v) =
  c->value |-> v &*& malloc_block_Counter(c);
@*/

// TODO: make this function pass the verification
bool my_random();
//@ requires true;
//@ ensures true;

bool my_random() {
    // Implementation of my_random can be anything that returns a boolean.
    // For example, it can return a random boolean value.
    return rand() % 2 == 0;
}