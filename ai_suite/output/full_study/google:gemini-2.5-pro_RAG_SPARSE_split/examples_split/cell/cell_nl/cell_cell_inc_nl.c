/*@
predicate cell_pred(struct cell *c; int x) =
    c->x |-> x &*& malloc_block_cell(c);
@*/
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

/*@

// A predicate representing ownership of a `cell` struct and its value.
// It is declared as precise (using ';') so that fractions can be merged.
predicate cell_pred(struct cell *c; int x) =
    c->x |-> x &*& malloc_block_cell(c);

@*/


// TODO: make this function pass the verification
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
    //@ requires cell_pred(c, ?old_x) &*& INT_MIN <= old_x + v && old_x + v <= INT_MAX;
    //@ ensures cell_pred(c, old_x + v);
{
    //@ open cell_pred(c, old_x);
    c->x += v;
    //@ close cell_pred(c, old_x + v);
}