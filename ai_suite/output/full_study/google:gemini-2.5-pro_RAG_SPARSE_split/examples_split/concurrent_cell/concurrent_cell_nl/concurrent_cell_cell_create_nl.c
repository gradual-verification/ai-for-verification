#include "threading.hh"
#include "stdlib.h"

struct cell {
  int x;
  struct mutex* mutex;
};

/*@

// This predicate serves as the invariant for the mutex.
// It owns the data that is protected by the mutex, i.e., the 'x' field of the cell.
// It is a predicate constructor, taking the cell pointer 'c' as a parameter.
predicate_ctor cell_inv(struct cell *c)() =
    c->x |-> _;

// This predicate represents ownership of a cell object.
// It owns the memory for the struct fields that are not protected by the mutex,
// the malloc_block for the cell, and the mutex itself.
// The semicolon indicates that 'c' is a precise parameter.
predicate cell(struct cell *c;) =
    c->mutex |-> ?m &*&
    malloc_block_cell(c) &*&
    mutex(m, cell_inv(c));

@*/


// TODO: make this function pass the verification
/*cell_create function
-param: none
-description: This function creates a new cell with an intialized mutex in it.

It returns a pointer to the newly created cell.
*/
struct cell* cell_create()
    //@ requires true;
    //@ ensures result == 0 ? emp : cell(result);
{
  struct cell* c = malloc(sizeof(struct cell));
  if(c == 0) return 0;
  c->x = 0;
  
  // To create a mutex, we must first establish its invariant.
  //@ close cell_inv(c)();
  
  // We pass the invariant to create_mutex via a ghost argument.
  //@ close create_mutex_ghost_arg(cell_inv(c));
  struct mutex* m = create_mutex();
  
  c->mutex = m;
  
  // Now that all parts are in place, we can close the main 'cell' predicate.
  //@ close cell(c);
  return c;
}