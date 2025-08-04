#include "threading.h"
#include "stdlib.h"

/*@

// A type for predicates that constrain the value of a cell.
// For example, `(is_positive)(v)` could be `v > 0`.
typedef predicate value_constraint(int v);

// The invariant of the mutex associated with a cell.
// It states that the mutex protects the cell's 'x' field, and that
// the value of 'x' always satisfies the constraint 'C'.
predicate_ctor cell_inv(struct cell *c, value_constraint *C)() =
    c->x |-> ?v &*& C(v);

// The main predicate for a cell.
// It ties the cell structure to its mutex and the value constraint.
// To own a 'cell', you must own its mutex and know the constraint.
predicate cell(struct cell *c, value_constraint *C) =
    c->mutex |-> ?m &*&
    mutex(m, cell_inv(c, C));

@*/

struct cell {
  int x;
  struct mutex* mutex;
};


// TODO: make this function pass the verification
/*get function
-param: struct cell* c
-description: This get function retrieves the current value of the `x` field in the given cell structure in a thread-safe manner (using mutex). 

Other operations can be finished concurrently during this operation, so this function makes sure that
the old trace is the prefix of the new trace. 

It returns the value of `x`.
*/
int get(struct cell* c)
    //@ requires [?f]cell(c, ?C);
    //@ ensures [f]cell(c, C) &*& C(result);
{
  int res;
  mutex_acquire(c->mutex);
  res = c->x;
  {
  }
  mutex_release(c->mutex);
  return res;
}
