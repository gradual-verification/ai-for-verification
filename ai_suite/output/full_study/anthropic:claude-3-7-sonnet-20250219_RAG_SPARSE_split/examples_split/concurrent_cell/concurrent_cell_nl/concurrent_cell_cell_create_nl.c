#include "threading.h"
#include "stdlib.h"

struct cell {
  int x;
  struct mutex* mutex;
};

/*@
// Define a predicate for the cell structure
predicate cell(struct cell* c; int value) =
  c->x |-> value &*& 
  c->mutex |-> ?m &*& 
  mutex(m, cell_inv(c)) &*& 
  malloc_block_cell(c);

// Define the mutex invariant
predicate_ctor cell_inv(struct cell* c)() = 
  c->x |-> ?value;
@*/

// TODO: make this function pass the verification
/*cell_create function
-param: none
-description: This function creates a new cell with an intialized mutex in it.

It returns a pointer to the newly created cell.
*/
struct cell* cell_create()
//@ requires true;
//@ ensures result == 0 ? true : cell(result, 0);
{
  struct cell* c = malloc(sizeof(struct cell));
  //@ if (c == 0) return 0;
  if(c == 0) return 0;
  c->x = 0;
  
  //@ close create_mutex_ghost_arg(cell_inv(c));
  //@ close cell_inv(c)();
  struct mutex* m = create_mutex();
  c->mutex = m;
  
  //@ close cell(c, 0);
  return c;
}