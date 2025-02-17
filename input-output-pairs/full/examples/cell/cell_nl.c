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
 * Creates a new `cell` and initializes it with the value `0`.
 *
 * @returns A pointer to a newly allocated `cell` object.
 *
 * Allocates memory for a `cell` structure, initializes the value to `0`, and returns a pointer to it.
 * If memory allocation fails, the program terminates.
 */
struct cell* create_cell() 
{
  struct cell* c = malloc(sizeof(struct cell));
  if (c == 0) abort();
  c->x = 0;
  return c;
}

/***
 * Description:
 * Sets the value of a `cell` to the given integer `v`.
 *
 * @param c - A pointer to the `cell` object.
 * @param v - The integer value to set.
 */
void cell_set(struct cell* c, int v)
{
  c->x = v;
}

/***
 * Description:
 * Increments the value of a `cell` by the given integer `v`.
 *
 * @param c - A pointer to the `cell` object.
 * @param v - The integer value to add to the current value.
 *
 * The function ensures that the result of the addition does not exceed the integer limits.
 */
void cell_inc(struct cell* c, int v)
{
  c->x += v;
}

/***
 * Description:
 * Retrieves the current value of a `cell`.
 *
 * @param c - A pointer to the `cell` object.
 * @returns The integer value stored in the `cell`.
 */
int cell_get(struct cell* c)
{
  return c->x;
}

/***
 * Description:
 * Swaps the values of two `cell` objects.
 *
 * @param c1 - A pointer to the first `cell`.
 * @param c2 - A pointer to the second `cell`.
 *
 * The function retrieves the values of both cells, swaps them, and stores the swapped values back.
 */
void cell_swap(struct cell* c1, struct cell* c2)
{
  int tmp1 = cell_get(c1);
  int tmp2 = cell_get(c2);
  cell_set(c1, tmp2);
  cell_set(c2, tmp1);
}

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

/***
 * Description:
 * Demonstrates the creation and manipulation of `cell` objects.
 *
 * The `main` function creates two cells, sets their values to `5` and `10`,
 * swaps their contents, verifies the swap, and disposes of the cells to free allocated memory.
 */
int main() 
{
  struct cell* c1 = create_cell();
  struct cell* c2 = create_cell();
  
  cell_set(c1, 5);
  cell_set(c2, 10);
  
  cell_swap(c1, c2); 
  
  int tmp = cell_get(c1);
  assert(tmp == 10);
  
  cell_dispose(c1);
  cell_dispose(c2);
  
  return 0;
}
