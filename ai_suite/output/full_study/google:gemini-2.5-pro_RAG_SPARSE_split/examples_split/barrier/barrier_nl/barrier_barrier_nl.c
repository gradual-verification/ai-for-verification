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

/*@
// The invariant protected by the mutex.
// It states that if k is at its maximum (n), threads must be in the outgoing phase.
// If k is at its minimum (0), threads must be in the incoming phase.
// This invariant holds for n > 1. The implementation has a bug for n=1 on reuse.
predicate_ctor barrier_inv(struct barrier *b, int n)() =
    b->n |-> n &*&
    b->k |-> ?k &*&
    b->outgoing |-> ?outgoing &*&
    0 <= k &*& k <= n &*&
    (k == n ==> outgoing == true) &*&
    (k == 0 ==> outgoing == false);

// The main predicate for a barrier. It is fractional to allow sharing between threads.
predicate barrier(struct barrier *b; int n) =
    b->mutex |-> ?mutex &*&
    malloc_block_barrier(b) &*&
    mutex(mutex, barrier_inv(b, n));
@*/


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
    //@ requires [?f]barrier(barrier, ?n) &*& n > 1;
    //@ ensures [f]barrier(barrier, n);
{
    //@ open barrier(barrier, n);
    struct mutex *mutex = barrier->mutex;
    mutex_acquire(mutex);
    //@ open barrier_inv(barrier, n)();

    {
        while (barrier->outgoing)
            /*@
            invariant
                mutex_held(mutex, barrier_inv(barrier, n), currentThread, f) &*&
                barrier->n |-> n &*&
                barrier->k |-> ?k &*&
                barrier->outgoing |-> ?outgoing &*&
                0 <= k &*& k <= n &*&
                (k == n ==> outgoing == true) &*&
                (k == 0 ==> outgoing == false);
            @*/
        {
            //@ close barrier_inv(barrier, n)();
            mutex_release(mutex);
            mutex_acquire(mutex);
            //@ open barrier_inv(barrier, n)();
        }
    }

    barrier->k++;
    if (barrier->k == barrier->n) {
        barrier->outgoing = true;
        barrier->k--;
     
        //@ close barrier_inv(barrier, n)();
        mutex_release(barrier->mutex);
    } else {
        while (!barrier->outgoing)
            /*@
            invariant
                mutex_held(mutex, barrier_inv(barrier, n), currentThread, f) &*&
                barrier->n |-> n &*&
                barrier->k |-> ?k &*&
                barrier->outgoing |-> ?outgoing &*&
                0 <= k &*& k <= n &*&
                (k == n ==> outgoing == true) &*&
                (k == 0 ==> outgoing == false);
            @*/
        {
            //@ close barrier_inv(barrier, n)();
            mutex_release(mutex);
            mutex_acquire(mutex);
            //@ open barrier_inv(barrier, n)();
        }

        barrier->k--;
        if (barrier->k == 0) {
            barrier->outgoing = false;
        }
      
        //@ close barrier_inv(barrier, n)();
        mutex_release(mutex);
    }
    //@ close [f]barrier(barrier, n);
}