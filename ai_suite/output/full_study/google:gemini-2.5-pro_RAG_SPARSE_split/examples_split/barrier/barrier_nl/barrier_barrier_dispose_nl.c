#include "stdlib.h"
#include "threading.h"

/*@
// A predicate for the invariant protected by the barrier's mutex.
// It holds the fields that are modified by multiple threads.
predicate_ctor barrier_inv(struct barrier *b)() =
    b->k |-> _ &*&
    b->outgoing |-> _;

// A predicate representing a valid, initialized barrier.
// It owns the barrier struct's memory and the associated mutex.
predicate barrier_pred(struct barrier *b; int n) =
    b->mutex |-> ?m &*&
    b->n |-> n &*&
    malloc_block_barrier(b) &*&
    mutex(m, barrier_inv(b));
@*/

/***
 * Description:
 * A barrier is a synchronization mechanism that allows multiple threads
 * to wait until they have all reached the same point of execution.
 * 
 * The structure holds:
 *  - A mutex to ensure mutual exclusion when accessing shared variables.
 *  - The total number of threads (n) that must arrive at the barrier.
 *  - A counter (k) to keep track of how many threads have arrived.
 *  - A boolean (outgoing) to indicate whether threads are being released
 *    from the barrier or are still arriving.
 */
struct barrier {
    struct mutex *mutex;
    int n;
    int k;
    bool outgoing;
};

/***
 * Description:
 * This structure holds shared data used by two threads that coordinate 
 * via the barrier. The fields `x1`, `x2`, `y1`, `y2`, and `i` are used 
 * as example variables manipulated by the threads.
 */
struct data {
    struct barrier *barrier;
    int x1;
    int x2;
    int y1;
    int y2;
    int i;
};


// TODO: make this function pass the verification
/***
 * Description:
 * Cleans up and deallocates the barrier once it is no longer needed.
 *
 * @param b - A pointer to the `struct barrier` to dispose of.
 *
 * The function disposes the underlying mutex and frees the memory
 * allocated for the barrier. After calling this function, the barrier
 * pointer must not be used again.
 */
void barrier_dispose(struct barrier *barrier)
    //@ requires barrier_pred(barrier, ?n);
    //@ ensures emp;
{
    //@ open barrier_pred(barrier, n);
    mutex_dispose(barrier->mutex);
    //@ open barrier_inv(barrier)();
    free(barrier);
}