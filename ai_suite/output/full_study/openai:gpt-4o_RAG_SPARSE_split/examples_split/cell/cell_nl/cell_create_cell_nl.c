#include "stdlib.h"

/***
 * Description:
 * This program defines a `cell` structure, a set of operations for managing its state,
 * and a demonstration of these operations in the `main` function. The `cell` is a simple wrapper
 * around an integer value with support for creation, updating, swapping, and disposal.
 */
struct cell {
  int x;
};

//@ predicate cell(struct cell *c; int x) = c->x |-> x &*& malloc_block_cell(c);

// TODO: make this function pass the verification
/***
 * Description:
 * Creates a new `cell` and initializes it with the value `0`.
 *
 * @returns A pointer to a newly allocated `cell` object.
 *
 * It makes sure that the return value is a cell with its x field as 0.
 */
//@ requires true;
//@ ensures result == 0 ? true : cell(result, 0);
struct cell* create_cell() 
{
  struct cell* c = malloc(sizeof(struct cell));
  if (c == 0) abort();
  c->x = 0;
  //@ close cell(c, 0);
  return c;
}