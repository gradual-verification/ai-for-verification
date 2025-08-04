#include "stdlib.h"

struct Counter {
  int value;
};

/*@
predicate Counter(struct Counter* c, int v) =
  c->value |-> v;
@*/


// This function is a declaration of an external function whose implementation is not provided.
// Therefore, we can only specify its contract. The contract below is the most general one possible.
// It does not require any specific state (requires true) and does not guarantee any specific
// state change (ensures true). This is a sound way to model an external function whose
// behavior is unknown or irrelevant to the properties being verified.
// VeriFast understands that a function returning 'bool' will result in either 'true' or 'false'.
bool random();
//@ requires true;
//@ ensures true;