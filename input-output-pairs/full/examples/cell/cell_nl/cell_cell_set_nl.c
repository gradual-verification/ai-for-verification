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


// TODO: make this function pass the verification
/***
 * Description:
 * Sets the value of a `cell` to the given integer `v`.
 *
 * @param c - A pointer to the `cell` object.
 * @param v - The integer value to set.
 * 
 * It makes sures that c has its x field set as v.
 */
void cell_set(struct cell* c, int v)
{
  c->x = v;
}

