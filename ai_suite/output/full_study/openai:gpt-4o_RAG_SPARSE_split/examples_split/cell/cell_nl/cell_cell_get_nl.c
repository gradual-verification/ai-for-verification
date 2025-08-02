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

//@ predicate cell(struct cell* c; int v) = c->x |-> v &*& malloc_block_cell(c);

// TODO: make this function pass the verification
/***
 * Description:
 * Retrieves the current value of a `cell`.
 *
 * @param c - A pointer to the `cell` object.
 * @returns The integer value stored in the `cell`.
 * 
 * It makes sure that the cell c is not changed and the return value is the x field of c.
 */
//@ requires cell(c, ?v);
//@ ensures cell(c, v) &*& result == v;
int cell_get(struct cell* c)
{
  return c->x;
}