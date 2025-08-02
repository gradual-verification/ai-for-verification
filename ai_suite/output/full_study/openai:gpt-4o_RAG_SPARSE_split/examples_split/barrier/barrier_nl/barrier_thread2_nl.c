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

predicate barrier(struct barrier *b, int n) =
    b->mutex |-> ?mutex &*&
    b->n |-> n &*&
    b->k |-> ?k &*&
    b->outgoing |-> ?outgoing &*&
    malloc_block_barrier(b) &*&
    mutex(mutex, barrier_inv(b, n));

predicate barrier_inv(struct barrier *b, int n)() =
    b->k |-> ?k &*&
    b->outgoing |-> ?outgoing &*&
    0 <= k &*& k <= n &*&
    (outgoing ? k >= 0 : k < n);

predicate data(struct data *d, struct barrier *b, int x1, int x2, int y1, int y2, int i) =
    d->barrier |-> b &*&
    d->x1 |-> x1 &*&
    d->x2 |-> x2 &*&
    d->y1 |-> y1 &*&
    d->y2 |-> y2 &*&
    d->i |-> i &*&
    malloc_block_data(d);

@*/

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
    //@ requires barrier(barrier, ?n);
    //@ ensures barrier(barrier, n);
{
    struct mutex *mutex = barrier->mutex;
    mutex_acquire(mutex);

    {
        while (barrier->outgoing)
        {
            mutex_release(mutex);
            mutex_acquire(mutex);
        }
    }

    barrier->k++;
    if (barrier->k == barrier->n) {
        barrier->outgoing = true;
        barrier->k--;
     
        mutex_release(barrier->mutex);
    } else {
        while (!barrier->outgoing)
        {
            mutex_release(mutex);
            mutex_acquire(mutex);
        }

        barrier->k--;
        if (barrier->k == 0) {
            barrier->outgoing = false;
        }
      
        mutex_release(mutex);
    }
}

// TODO: make this function pass the verification
/***
 * Description:
 * The second worker thread function. It performs similar operations 
 * to `thread1` but with different internal calculations on `x1`, `x2`, 
 * `y1`, and `y2`, also repeatedly waiting at the same barrier to stay 
 * in sync with the first thread. It first updates `y2` based on `x1` and `x2`,
 * and then updates `x2` based on `y1` and `y2`
 *
 * @param d - A pointer to the shared `struct data`.
 */
void thread2(struct data *d)
    //@ requires data(d, ?b, ?x1, ?x2, ?y1, ?y2, ?i) &*& barrier(b, ?n);
    //@ ensures data(d, b, ?nx1, ?nx2, ?ny1, ?ny2, ?ni) &*& barrier(b, n);
{
    struct barrier *barrier = d->barrier;
    {
        barrier(barrier);
    }
    int m = 0;
    while (m < 30)
    //@ invariant data(d, barrier, ?x1_, ?x2_, ?y1_, ?y2_, ?i_) &*& barrier(barrier, n);
    {
        int a1 = d->x1;
        int a2 = d->x2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->y2 = a1 + 3 * a2;
        {
            barrier(barrier);
        }
        a1 = d->y1;
        a2 = d->y2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->x2 = a1 + 3 * a2;
        {
            barrier(barrier);
        }
        m = d->i;
    }
    {
        barrier(barrier);
    }
}