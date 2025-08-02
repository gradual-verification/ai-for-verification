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

//@ predicate barrier_inv(struct barrier *b)() =
//@     b->n |-> ?n &*& b->k |-> ?k &*& b->outgoing |-> ?outgoing &*&
//@     0 <= k &*& k <= n &*& (outgoing ? k < n : true);

// TODO: make this function pass the verification
/***
 * Description:
 * Waits at the barrier until all `n` threads have arrived. Once all have 
 * arrived, the barrier transitions to release them. After the last thread 
 * leaves, the barrier is exited and reset.
 *
 * @param b - A pointer to the `struct barrier` on which to wait.
 *
 * This function uses a mutex to coordinate increments of the arrival counter 
 * (`k`) and to handle the barrier’s `outgoing` flag. Threads spin inside 
 * critical sections (by releasing and reacquiring the mutex) until the 
 * barrier state changes appropriately.
 * 
 * It requires that the barrier is incoming at the beginning, and makes sure that
 * the barrier is exiting at the end.
 */
void barrier(struct barrier *barrier)
    //@ requires barrier(barrier, ?n, ?k, false);
    //@ ensures barrier(barrier, n, 0, false);
{
    struct mutex *mutex = barrier->mutex;
    mutex_acquire(mutex);
    //@ open barrier_inv(barrier)();

    while (barrier->outgoing)
        //@ invariant barrier_inv(barrier)();
    {
        mutex_release(mutex);
        mutex_acquire(mutex);
        //@ open barrier_inv(barrier)();
    }

    barrier->k++;
    if (barrier->k == barrier->n) {
        barrier->outgoing = true;
        barrier->k--;
        //@ close barrier_inv(barrier)();
        mutex_release(barrier->mutex);
    } else {
        while (!barrier->outgoing)
            //@ invariant barrier_inv(barrier)();
        {
            mutex_release(mutex);
            mutex_acquire(mutex);
            //@ open barrier_inv(barrier)();
        }

        barrier->k--;
        if (barrier->k == 0) {
            barrier->outgoing = false;
        }
        //@ close barrier_inv(barrier)();
        mutex_release(mutex);
    }
    //@ close barrier(barrier, n, 0, false);
}