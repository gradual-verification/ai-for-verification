#include "threading.h"
#include "stdlib.h"

struct cell {
  int x;
  struct mutex* mutex;
};

//@ predicate cell(struct cell* c; int x) = 
//@   c->x |-> x &*& c->mutex |-> ?m &*& malloc_block_cell(c) &*& mutex(m, cell_mutex_inv(c));

/*@ predicate cell_mutex_inv(struct cell* c) = 
  c->x |-> _; 
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
  if(c == 0) return 0;
  c->x = 0;
  //@ close create_mutex_ghost_arg(cell_mutex_inv(c));
  struct mutex* m = create_mutex();
  c->mutex = m;
  //@ close cell(c, 0);
  return c;
}