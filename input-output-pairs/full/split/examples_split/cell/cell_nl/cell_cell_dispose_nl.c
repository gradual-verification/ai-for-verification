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
 * Disposes of a `cell` object and frees its allocated memory.
 *
 * @param c - A pointer to the `cell` object.
 *
 * The function releases the memory allocated for the `cell` to avoid memory leaks.
 */
void cell_dispose(struct cell* c) 
{
  free(c);
}

