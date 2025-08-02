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


//@ predicate cell(struct cell* c, int value) = c->x |-> value &*& malloc_block_cell(c);

/***
 * Description:
 * Increments the value of a `cell` by the given integer `v`.
 *
 * @param c - A pointer to the `cell` object.
 * @param v - The integer value to add to the current value.
 *
 * It makes sures that c has its x field incremented by v.
 */
void cell_inc(struct cell* c, int v)
//@ requires cell(c, ?old_value) &*& INT_MIN <= old_value + v &*& old_value + v <= INT_MAX;
//@ ensures cell(c, old_value + v);
{
  //@ open cell(c, old_value);
  c->x += v;
  //@ close cell(c, old_value + v);
}