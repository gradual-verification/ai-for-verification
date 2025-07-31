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


/***
 * Description:
 * Retrieves the current value of a `cell`.
 *
 * @param c - A pointer to the `cell` object.
 * @returns The integer value stored in the `cell`.
 * 
 * It makes sure that the cell c is not changed and the return value is the x field of c.
 */
int cell_get(struct cell* c)
{
  return c->x;
}


// TODO: make this function pass the verification
/***
 * Description:
 * Swaps the values of two `cell` objects.
 *
 * @param c1 - A pointer to the first `cell`.
 * @param c2 - A pointer to the second `cell`.
 *
 * The function makes sure that the x fields in c1 and c2 are swapped.
 */
void cell_swap(struct cell* c1, struct cell* c2)
{
  int tmp1 = cell_get(c1);
  int tmp2 = cell_get(c2);
  cell_set(c1, tmp2);
  cell_set(c2, tmp1);
}

