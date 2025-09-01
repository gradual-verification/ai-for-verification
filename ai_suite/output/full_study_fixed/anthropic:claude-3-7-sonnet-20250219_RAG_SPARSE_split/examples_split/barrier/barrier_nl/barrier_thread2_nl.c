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
// Predicate to represent the barrier invariant
predicate_ctor barrier_inv(struct barrier *b)() = 
    b->n |-> ?n &*& 
    b->k |-> ?k &*& 
    b->outgoing |-> ?outgoing &*& 
    n > 0 &*& 
    0 <= k &*& k <= n;

// Predicate for a barrier
predicate barrier(struct barrier *b, int n) = 
    b->mutex |-> ?m &*& 
    mutex(m, barrier_inv(b)) &*& 
    malloc_block_barrier(b) &*&
    b->n |-> n &*&
    n > 0;
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
//@ requires barrier->mutex |-> ?m &*& mutex(m, barrier_inv(barrier));
//@ ensures barrier->mutex |-> m &*& mutex(m, barrier_inv(barrier));
{
    struct mutex *mutex = barrier->mutex;
    mutex_acquire(mutex);
    //@ open barrier_inv(barrier)();

    {
        while (barrier->outgoing)
        //@ invariant barrier->n |-> ?n &*& barrier->k |-> ?k &*& barrier->outgoing |-> ?outgoing &*& n > 0 &*& 0 <= k &*& k <= n &*& mutex_held(mutex, barrier_inv(barrier), currentThread, _);
        {
            //@ close barrier_inv(barrier)();
            mutex_release(mutex);
            mutex_acquire(mutex);
            //@ open barrier_inv(barrier)();
        }
    }

    barrier->k++;
    if (barrier->k == barrier->n) {
        barrier->outgoing = true;
        barrier->k--;
        //@ close barrier_inv(barrier)();
        mutex_release(barrier->mutex);
    } else {
        while (!barrier->outgoing)
        //@ invariant barrier->n |-> ?n &*& barrier->k |-> ?k &*& barrier->outgoing |-> ?outgoing &*& n > 0 &*& 0 <= k &*& k <= n &*& mutex_held(mutex, barrier_inv(barrier), currentThread, _);
        {
            //@ close barrier_inv(barrier)();
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
}

/*@
// Predicate for thread2's data
predicate thread2_data(struct data *d) =
    d->barrier |-> ?b &*&
    barrier->mutex |-> ?m &*&
    mutex(m, barrier_inv(b)) &*&
    d->x1 |-> ?x1 &*&
    d->x2 |-> ?x2 &*&
    d->y1 |-> ?y1 &*&
    d->y2 |-> ?y2 &*&
    d->i |-> ?i &*&
    malloc_block_data(d);

// Predicate family for thread2 function
predicate_family_instance thread_run_data(thread2)(struct data *d) =
    thread2_data(d);
@*/

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
//@ requires thread_run_data(thread2)(d);
//@ ensures true;
{
    //@ open thread_run_data(thread2)(d);
    struct barrier *b = d->barrier;
    {
        barrier(b);
    }
    int m = 0;
    while (m < 30)
    //@ invariant d->barrier |-> b &*& b->mutex |-> ?mutex &*& mutex(mutex, barrier_inv(b)) &*& d->i |-> ?i &*& d->x1 |-> ?x1 &*& d->x2 |-> ?x2 &*& d->y1 |-> ?y1 &*& d->y2 |-> ?y2 &*& malloc_block_data(d) &*& 0 <= m;
    {
        int a1 = d->x1;
        int a2 = d->x2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->y2 = a1 + 3 * a2;
        {
            barrier(b);
        }
        a1 = d->y1;
        a2 = d->y2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->x2 = a1 + 3 * a2;
        {
            barrier(b);
        }
        m = d->i;
    }
    {
        barrier(b);
    }
}