#include "stdlib.h"

struct Counter {
  int value;
};

/*@
predicate Counter(struct Counter* c, int v) =
  c->value |-> v &*& malloc_block_Counter(c);
@*/


/**
 * This function models an external, non-deterministic function that returns a boolean value.
 * The contract `requires true; ensures true;` is the standard way to specify such a function in VeriFast.
 * It means the function can be called in any state, and it does not provide any information about
 * its return value, other than its type. The verifier will consider both possible return values (true and false)
 * in any path following a call to this function.
 */
bool random();
//@ requires true;
//@ ensures true;
