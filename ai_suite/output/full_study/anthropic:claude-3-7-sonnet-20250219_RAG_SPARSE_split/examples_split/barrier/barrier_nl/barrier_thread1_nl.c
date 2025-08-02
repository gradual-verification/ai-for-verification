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

/*@
// Predicate to represent the barrier's state
predicate_ctor barrier_state(struct barrier *b)() =
    b->n |-> ?n &*& b->k |-> ?k &*& b->outgoing |-> ?outgoing &*&
    n > 0 &*& 0 <= k &*& k <= n;
@*/

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
// Predicate to represent the data structure's state
predicate data_state(struct data *d) =
    d->barrier |-> ?b &*& 
    d->x1 |-> ?x1 &*& d->x2 |-> ?x2 &*& 
    d->y1 |-> ?y1 &*& d->y2 |-> ?y2 &*& 
    d->i |-> ?i &*&
    0 <= x1 &*& x1 <= 1000 &*& 
    0 <= x2 &*& x2 <= 1000 &*& 
    0 <= y1 &*& y1 <= 1000 &*& 
    0 <= y2 &*& y2 <= 1000;
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
 * (`k`) and to handle the barrier's `outgoing` flag. Threads spin inside 
 * critical sections (by releasing and reacquiring the mutex) until the 
 * barrier state changes appropriately.
 * 
 * It requires that the barrier is incoming at the beginning, and makes sure that
 * the barrier is exiting at the end.
 */
void barrier(struct barrier *barrier)
//@ requires [?f]barrier->mutex |-> ?mutex &*& [f]mutex(mutex, barrier_state(barrier));
//@ ensures [f]barrier->mutex |-> mutex &*& [f]mutex(mutex, barrier_state(barrier));
{
    struct mutex *mutex = barrier->mutex;
    mutex_acquire(mutex);
    //@ open barrier_state(barrier)();

    {
        while (barrier->outgoing)
        //@ invariant barrier->n |-> ?n &*& barrier->k |-> ?k &*& barrier->outgoing |-> ?outgoing &*& n > 0 &*& 0 <= k &*& k <= n;
        {
            mutex_release(mutex);
            mutex_acquire(mutex);
        }
    }

    barrier->k++;
    if (barrier->k == barrier->n) {
        barrier->outgoing = true;
        barrier->k--;
        //@ close barrier_state(barrier)();
        mutex_release(barrier->mutex);
    } else {
        while (!barrier->outgoing)
        //@ invariant barrier->n |-> ?n &*& barrier->k |-> ?k &*& barrier->outgoing |-> ?outgoing &*& n > 0 &*& 0 <= k &*& k <= n;
        {
            mutex_release(mutex);
            mutex_acquire(mutex);
        }

        barrier->k--;
        if (barrier->k == 0) {
            barrier->outgoing = false;
        }
        //@ close barrier_state(barrier)();
        mutex_release(mutex);
    }
}

/***
 * Description:
 * The first worker thread function. It repeatedly uses the barrier to
 * coordinate with the other thread while manipulating the fields `x1`,
 * `x2`, `y1`, and `y2` in the shared `struct data`.
 *
 * @param d - A pointer to the shared `struct data`.
 *
 * The thread checks boundaries on `x1` and `x2`, updates `y1` based on 
 * calculations, then waits at the barrier. It continues updating `x1` based on `y1` and `y2` and 
 * synchronizing until it finishes its loop, then sets `d->i` to 0 before
 * returning.
 */
void thread1(struct data *d)
//@ requires data_state(d) &*& [?f]d->barrier->mutex |-> ?mutex &*& [f]mutex(mutex, barrier_state(d->barrier));
//@ ensures data_state(d) &*& [f]d->barrier->mutex |-> mutex &*& [f]mutex(mutex, barrier_state(d->barrier));
{
    struct barrier *barrier = d->barrier;
    {
        barrier(barrier);
    }
    int N = 0;
    while (N < 30)
    //@ invariant data_state(d) &*& [f]d->barrier->mutex |-> mutex &*& [f]mutex(mutex, barrier_state(d->barrier)) &*& 0 <= N &*& N <= 30;
    {
        int a1 = d->x1;
        int a2 = d->x2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->y1 = a1 + 2 * a2;
        {
            barrier(barrier);
        }
        a1 = d->y1;
        a2 = d->y2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->x1 = a1 + 2 * a2;
        N = N + 1;
        d->i = N;
        {
            barrier(barrier);
        }
    }
    {
        barrier(barrier);
    }
    d->i = 0;
}