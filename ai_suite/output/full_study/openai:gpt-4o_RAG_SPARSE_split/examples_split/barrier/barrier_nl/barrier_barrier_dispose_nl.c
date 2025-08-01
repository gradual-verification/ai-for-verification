#include "stdlib.h"
#include "threading.h"

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

//@ predicate barrier(struct barrier *b; int n, int k, bool outgoing) =
//@     b->mutex |-> ?mutex &*& mutex(mutex, barrier_inv(b)) &*&
//@     b->n |-> n &*& b->k |-> k &*& b->outgoing |-> outgoing;

//@ predicate barrier_inv(struct barrier *b) =
//@     b->n |-> ?n &*& b->k |-> ?k &*& b->outgoing |-> ?outgoing;

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
// TODO: make this function pass the verification
void barrier_dispose(struct barrier *barrier)
    //@ requires barrier(barrier, ?n, ?k, ?outgoing);
    //@ ensures true;
{
    //@ open barrier(barrier, n, k, outgoing);
    mutex_dispose(barrier->mutex);
    free(barrier);
}