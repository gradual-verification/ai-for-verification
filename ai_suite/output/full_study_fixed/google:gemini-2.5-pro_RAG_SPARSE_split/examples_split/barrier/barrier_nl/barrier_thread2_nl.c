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

// Predicate to hold the logical phase of the computation.
// It's precise, so fractions can be merged, and the phase is consistent.
predicate barrier_phase(struct barrier *b; int phase);

// Predicate for the barrier's mutex invariant.
// It holds the physical state of the barrier and the logical phase.
predicate_ctor barrier_inv(struct barrier *b)() =
    b->n |-> ?n &*&
    b->k |-> ?k &*&
    b->outgoing |-> ?out &*&
    barrier_phase(b, ?phase) &*&
    0 <= k &*& k <= n;

// Predicate representing the full barrier object, including its mutex.
predicate is_barrier(struct barrier *b) =
    b->mutex |-> ?m &*& mutex(m, barrier_inv(b));

// Predicate for the shared data fields and their bounds.
predicate data_fields(struct data *d, int x1, int x2, int y1, int y2, int i) =
    d->x1 |-> x1 &*&
    d->x2 |-> x2 &*&
    d->y1 |-> y1 &*&
    d->y2 |-> y2 &*&
    d->i |-> i &*&
    0 <= x1 &*& x1 <= 1000 &*&
    0 <= x2 &*& x2 <= 1000 &*&
    0 <= y1 &*& y1 <= 4000 &*& // Bounds adjusted for computation results
    0 <= y2 &*& y2 <= 4000;

// Predicate for the permissions required by a thread in a given phase.
// phase 1: compute y's from x's.
// phase 2: compute x's from y's.
predicate thread_perm(int thread_id, int phase, struct data *d) =
    d->barrier |-> ?b &*& [1/2]is_barrier(b) &*&
    (
        phase == 1 ?
            // Phase 1: Read x's, write y's
            thread_id == 1 ?
                [1/2]data_fields(d, ?x1, ?x2, _, _, ?i) &*& d->y1 |-> _
            : // thread_id == 2
                [1/2]data_fields(d, ?x1, ?x2, _, _, ?i) &*& d->y2 |-> _
        : // phase == 2
            // Phase 2: Read y's, write x's
            thread_id == 1 ?
                [1/2]data_fields(d, _, _, ?y1, ?y2, _) &*& d->x1 |-> _ &*& d->i |-> _
            : // thread_id == 2
                [1/2]data_fields(d, _, _, ?y1, ?y2, _) &*& d->x2 |-> _
    );

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
void barrier(struct barrier *b)
    /*@ requires thread_perm(?tid, ?p, ?d) &*& d->barrier |-> b; @*/
    /*@ ensures  thread_perm(tid, p == 1 ? 2 : 1, d) &*& d->barrier |-> b; @*/
{
    //@ open thread_perm(tid, p, d);
    struct mutex *mutex = b->mutex;
    mutex_acquire(mutex);
    //@ open barrier_inv(b)();

    {
        while (b->outgoing)
        /*@ invariant b->mutex |-> mutex &*& b->n |-> ?n &*& b->k |-> ?k &*& b->outgoing |-> true &*&
                      barrier_phase(b, ?phase) &*&
                      mutex_held(mutex, barrier_inv(b), currentThread, 1/2);
        @*/
        {
            //@ close barrier_inv(b)();
            mutex_release(mutex);
            mutex_acquire(mutex);
            //@ open barrier_inv(b)();
        }
    }

    b->k++;
    if (b->k == b->n) {
        //@ open barrier_phase(b, p);
        //@ close barrier_phase(b, p == 1 ? 2 : 1);
        b->outgoing = true;
        b->k--;
     
        //@ close barrier_inv(b)();
        mutex_release(b->mutex);
    } else {
        while (!b->outgoing)
        /*@ invariant b->mutex |-> mutex &*& b->n |-> ?n &*& b->k |-> ?k &*& b->outgoing |-> false &*&
                      k > 0 &*& k < n &*&
                      barrier_phase(b, ?phase) &*&
                      mutex_held(mutex, barrier_inv(b), currentThread, 1/2);
        @*/
        {
            //@ close barrier_inv(b)();
            mutex_release(mutex);
            mutex_acquire(mutex);
            //@ open barrier_inv(b)();
        }

        b->k--;
        if (b->k == 0) {
            b->outgoing = false;
        }
      
        //@ close barrier_inv(b)();
        mutex_release(b->mutex);
    }
    //@ close thread_perm(tid, p == 1 ? 2 : 1, d);
}

/*@
// Predicate for the data passed to the thread.
// It sets up the initial permissions for thread 2 in phase 1.
predicate_family_instance thread_run_data(thread2)(struct data *d) =
    thread_perm(2, 1, d);
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
void thread2(struct data *d) //@ : thread_run
    //@ requires thread_run_data(thread2)(d) &*& lockset(currentThread, nil);
    //@ ensures lockset(currentThread, nil);
{
    //@ open thread_run_data(thread2)(d);
    struct barrier *b = d->barrier;
    {
        barrier(b);
    }
    int m = 0;
    while (m < 30)
        //@ invariant thread_perm(2, 2, d) &*& d->i |-> m;
    {
        //@ open thread_perm(2, 2, d);
        //@ open data_fields(d, _, _, ?y1, ?y2, _);
        int a1 = d->y1;
        int a2 = d->y2;
        if (a1 < 0 || a1 > 4000 || a2 < 0 || a2 > 4000) {abort();}
        d->x2 = a1 + 3 * a2;
        //@ close data_fields(d, _, _, y1, y2, _);
        //@ close thread_perm(2, 1, d);
        {
            barrier(b);
        }
        //@ open thread_perm(2, 1, d);
        //@ open data_fields(d, ?x1, ?x2, _, _, _);
        a1 = d->x1;
        a2 = d->x2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->y2 = a1 + 3 * a2;
        //@ close data_fields(d, x1, x2, _, _, _);
        //@ close thread_perm(2, 2, d);
        {
            barrier(b);
        }
        //@ open thread_perm(2, 2, d);
        //@ open data_fields(d, _, _, _, _, ?i);
        m = d->i;
        //@ close data_fields(d, _, _, _, _, i);
        //@ close thread_perm(2, 2, d);
    }
    {
        barrier(b);
    }
    //@ open thread_perm(2, 1, d);
    //@ leak thread_perm(2, 1, d);
}