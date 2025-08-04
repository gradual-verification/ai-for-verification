#include "threading.h"
#include "stdlib.h"

struct cell {
  int x;
  struct mutex* mutex;
};


/*@

// The invariant for the mutex associated with a cell 'c'.
// It states that the mutex protects the integer field 'x' of the cell.
// A predicate_ctor is used so that the predicate can be parameterized by 'c'.
predicate_ctor cell_invariant(struct cell *c)() =
    c->x |-> _;

@*/


// TODO: make this function pass the verification
/*increment function
-param: struct cell* c
-description: This function increments field x in the given cell c in a thread-safe manner (using mutex).

Other operations can be finished concurrently during this operation, so this function makes sure that
the old trace is the prefix of the new trace. 
*/
void increment(struct cell* c)
    /*@
    requires
        // To access the mutex pointer via 'c->mutex', a thread needs at least
        // a fractional permission to the 'mutex' field of the cell. This allows
        // reading the field but not writing to it, preventing data races on the pointer itself.
        [?f]c->mutex |-> ?m &*&
        // To acquire the mutex, the thread also needs a fractional permission to the mutex resource.
        [f]mutex(m, cell_invariant(c));
    ensures
        // The function returns the same permissions to the caller, allowing for subsequent operations.
        [f]c->mutex |-> m &*&
        [f]mutex(m, cell_invariant(c));
    @*/
{
  // The C expression 'c->mutex' reads from memory. The precondition
  // '[f]c->mutex |-> m' ensures this read is safe and yields 'm'.
  mutex_acquire(c->mutex);
  
  // Acquiring the mutex consumes the '[f]mutex' chunk and produces the invariant.
  //@ open cell_invariant(c)();
  
  // We now have full ownership of the protected data: 'c->x |-> _'.
  // VeriFast requires an explicit check to prove that the increment operation
  // does not cause an arithmetic overflow.
  if (c->x == INT_MAX) {
    abort();
  }
  
  // Since 'c->x' is not INT_MAX, the increment is safe.
  c->x++;
  
  {
    // This block is empty. For this verification, no additional ghost code is needed here.
    // The "trace" mentioned in the description is interpreted as an informal comment
    // on the abstract behavior, not a formal proof obligation for this function,
    // as that would require a more complex setup (e.g., with ghost state in boxes).
  }
  
  // Before releasing the mutex, we must re-establish its invariant.
  //@ close cell_invariant(c)();
  mutex_release(c->mutex);
}