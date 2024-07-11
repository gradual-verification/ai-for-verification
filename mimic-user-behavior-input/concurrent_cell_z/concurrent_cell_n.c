#include "threading.h"

struct cell {
  int x;
  struct mutex* mutex;
  //@ box id;
};



/**
 * Description:
 * The cell_create function is responsible for creating and initializing a new cell structure. It allocates memory for the cell, sets its initial values, and initializes a mutex for thread-safe operations. If the memory allocation fails, it returns a null pointer.
 *

 */
struct cell* cell_create()
{
 
  struct cell* c = malloc(sizeof(struct cell));
  if(c == 0) return 0;
  c->x = 0;

  struct mutex* m = create_mutex();
  c->mutex = m;
  return c;
}


/**
 * Description:
 * The increment function safely increments the x value of a given cell structure. 
 It uses a mutex to ensure that the operation is thread-safe, preventing concurrent modifications to the cell's x value.
 *
 * @param c A pointer to the cell structure to be incremented. The pointer must not be NULL.

 */
void increment(struct cell* c)
{

  mutex_acquire(c->mutex);
 
  c->x++;

  {
  
  }

  mutex_release(c->mutex);
}



/**
 * Description:
 * The decrement function safely decrements the x value of a given cell structure. 
 It uses a mutex to ensure that the operation is thread-safe, preventing concurrent modifications to the cell's x value.
 *
 * @param c A pointer to the cell structure to be decremented. The pointer must not be NULL.

 */
void decrement(struct cell* c)
{

  mutex_acquire(c->mutex);
 
  c->x--;

  {
    
  }

  mutex_release(c->mutex);
}



/**
 * Description:
 * The `cas` function (compare-and-swap) checks if the current value of `x` in the given cell structure is equal to `old`. If it is, the function updates `x` to `new`. This operation is thread-safe due to the use of a mutex.
 *
 * @param c A pointer to the cell structure.
 * @param old The value to compare against the current value of `x`.
 * @param new The value to set `x` to if the current value of `x` is equal to `old`.
 * @return The original value of `x` before the operation.

 */
int cas(struct cell* c, int old, int new)
{
 
  int res;
  mutex_acquire(c->mutex);

  res = c->x;
  if(c->x == old) {
    c->x = new;
  }

  {
    
  }

  mutex_release(c->mutex);
  return res;
}
/**
 * Description:
 * The `get` function retrieves the current value of the `x` field in the given cell structure.
 *
 * @param c A pointer to the cell structure.
 * @return The current value of the `x` field in the cell.
 * @requires c != NULL;
 */
int get(struct cell* c)
{

  int res;
  mutex_acquire(c->mutex);
  
  res = c->x;
 
  {
 
  }

  mutex_release(c->mutex);
  return res;
}


/**
 * Description:
 * The `only_allow_incrementing` function ensures that the value of the `x` field in the given cell structure
 * can only be incremented, not decremented or changed in any other way.
 *
 * @param c A pointer to the cell structure.
 * @requires c != NULL;
 */
only_allow_incrementing(struct cell* c)
{
  int x1 = get(c);
 
  int x2 = get(c);

  assert x1 <= x2;

}
