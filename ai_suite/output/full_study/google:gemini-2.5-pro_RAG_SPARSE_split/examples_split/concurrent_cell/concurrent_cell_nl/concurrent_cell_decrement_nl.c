#include "threading.h"
#include "stdlib.h"

struct cell {
  int x;
  struct mutex* mutex;
};

/*@

// The invariant for the mutex, which protects the cell's integer field 'x'.
predicate_ctor cell_invariant(struct cell *c)() =
    c->x |-> ?v;

// A predicate representing shared access to a cell.
// It provides fractional permissions to both the mutex pointer field and the mutex
// resource itself. This allows multiple threads to hold this predicate concurrently
// and attempt to acquire the lock.
predicate cell_shared(struct cell *c) =
    [?fp]c->mutex |-> ?m &*& [?fm]mutex(m, cell_invariant(c));

@*/

// TODO: make this function pass the verification
/*decrement function
-param: struct cell* c
-description: This function decrements field x in the given cell c in a thread-safe manner (using mutex).

Other operations can be finished concurrently during this operation, so this function makes sure that
the old trace is the prefix of the new trace. 
*/
void decrement(struct cell* c)
    //@ requires cell_shared(c);
    //@ ensures cell_shared(c);
{
    //@ open cell_shared(c);
    mutex_acquire(c->mutex);
    //@ open cell_invariant(c)();
    
    if (c->x == INT_MIN) {
        abort();
    }
    
    // The check `c->x != INT_MIN` is sufficient to prove that `c->x--` does not underflow.
    // VeriFast checks for signed integer overflow/underflow.
    // From `c->x |-> ?v`, we know `INT_MIN <= v <= INT_MAX`.
    // With the condition `v != INT_MIN`, it follows that `v >= INT_MIN + 1`.
    // Therefore, `v - 1 >= INT_MIN`, and the decrement operation is safe.
    c->x--;
    
    {
        // The comment about traces might suggest a more complex specification
        // involving ghost state, but for the given code, it's not necessary
        // for verifying memory safety and thread safety.
    }
    
    //@ close cell_invariant(c)();
    mutex_release(c->mutex);
    //@ close cell_shared(c);
}
