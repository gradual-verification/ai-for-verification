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
// Predicate to assert that a value is within the required bounds.
predicate bounds(int v) = 0 <= v && v <= 1000;

// Predicate for the state where x1 and x2 are readable and y1, y2 are writable.
predicate data_phase_x(struct data *d) =
    d->x1 |-> ?x1 &*& d->x2 |-> ?x2 &*& d->y1 |-> _ &*& d->y2 |-> _ &*&
    bounds(x1) &*& bounds(x2);

// Predicate for the state where y1 and y2 are readable and x1, x2 are writable.
predicate data_phase_y(struct data *d) =
    d->x1 |-> _ &*& d->x2 |-> _ &*& d->y1 |-> ?y1 &*& d->y2 |-> ?y2 &*&
    bounds(y1) &*& bounds(y2);

// The invariant for the barrier's mutex. It uses a ghost 'phase' variable
// to track which state the shared data is in.
predicate_ctor barrier_inv(struct barrier *b, struct data *d, int *phase)() =
    b->n |-> 2 &*& b->k |-> ?k &*& b->outgoing |-> ?is_outgoing &*& 0 <= k &*& k <= 2 &*&
    *phase |-> ?p &*&
    (is_outgoing ?
        (p == 0 ? data_phase_y(d) : data_phase_x(d))
    :
        (p == 0 ? data_phase_x(d) : data_phase_y(d))
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
    //@ requires [?f]b->mutex |-> ?m &*& [f]mutex(m, barrier_inv(b, ?d, ?phase));
    //@ ensures [f]b->mutex |-> m &*& [f]mutex(m, barrier_inv(b, d, phase));
{
    struct mutex *mutex = b->mutex;
    mutex_acquire(mutex);
    //@ open barrier_inv(b, d, phase)();
    //@ int p_old = *phase;

    while (b->outgoing)
        /*@ invariant mutex_held(mutex, barrier_inv(b, d, phase), currentThread, f) &*&
            b->n |-> 2 &*& b->k |-> ?k_loop &*& b->outgoing |-> true &*& 0 <= k_loop &*& k_loop <= 2 &*&
            *phase |-> p_old &*&
            (p_old == 0 ? data_phase_y(d) : data_phase_x(d));
        @*/
    {
        //@ close barrier_inv(b, d, phase)();
        mutex_release(mutex);
        mutex_acquire(mutex);
        //@ open barrier_inv(b, d, phase)();
        //@ assert *phase == p_old;
    }
    //@ assert b->outgoing |-> false;
    //@ assert *phase == p_old;

    b->k++;
    if (b->k == b->n) {
        b->outgoing = true;
        b->k--;
        //@ *phase = 1 - p_old;
        //@ if (p_old == 0) { open data_phase_x(d); close data_phase_y(d); } else { open data_phase_y(d); close data_phase_x(d); }
        //@ close barrier_inv(b, d, phase)();
        mutex_release(b->mutex);
    } else {
        //@ if (p_old == 0) { open data_phase_x(d); } else { open data_phase_y(d); }
        while (!b->outgoing)
            /*@ invariant mutex_held(mutex, barrier_inv(b, d, phase), currentThread, f) &*&
                b->n |-> 2 &*& b->k |-> 1 &*& b->outgoing |-> false &*&
                *phase |-> p_old &*&
                (p_old == 0 ? data_phase_x(d) : data_phase_y(d));
            @*/
        {
            //@ close barrier_inv(b, d, phase)();
            mutex_release(mutex);
            mutex_acquire(mutex);
            //@ open barrier_inv(b, d, phase)();
            //@ assert b->outgoing |-> true;
            //@ assert *phase |-> 1 - p_old;
        }
        //@ assert b->outgoing |-> true;
        //@ assert *phase |-> 1 - p_old;
        //@ if (*phase == 0) { open data_phase_y(d); } else { open data_phase_x(d); }

        b->k--;
        if (b->k == 0) {
            b->outgoing = false;
        }
        //@ if (*phase == 0) { close data_phase_y(d); } else { close data_phase_x(d); }
        //@ close barrier_inv(b, d, phase)();
        mutex_release(mutex);
    }
}

/*@
// Predicate for the resources held by thread1.
// It holds a fraction of the mutex and full ownership of the 'i' field.
predicate thread_share(struct data *d, int *phase) =
    d->barrier |-> ?b &*& b->mutex |-> ?m &*&
    [1/2]mutex(m, barrier_inv(b, d, phase)) &*&
    d->i |-> _;

// Predicate families to define the contract for thread1.
predicate_family thread_run_pre(thread1)(void *data, pair<int *, int> info);
predicate_family thread_run_post(thread1)(void *data, pair<int *, int> info);

predicate_family_instance thread_run_pre(thread1)(void *data, pair<int *, int> info) =
    let d = (struct data *)data;
    let phase = fst(info);
    let initial_phase = snd(info);
    thread_share(d, phase) &*&
    *phase |-> initial_phase;

predicate_family_instance thread_run_post(thread1)(void *data, pair<int *, int> info) =
    let d = (struct data *)data;
    let phase = fst(info);
    thread_share(d, phase) &*&
    d->i |-> 0 &*&
    *phase |-> _;
@*/

// TODO: make this function pass the verification
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
    //@ requires thread_run_pre(thread1)(d, ?info);
    //@ ensures thread_run_post(thread1)(d, info);
{
    //@ open thread_run_pre(thread1)(d, info);
    //@ pair<int *, int> info_ = info;
    //@ int *phase = fst(info_);
    //@ int initial_phase = snd(info_);
   
    struct barrier *b = d->barrier;
    {
        //@ open thread_share(d, phase);
        barrier(b);
        //@ close thread_share(d, phase);
    }
    int N = 0;
    while (N < 30)
        /*@ invariant N >= 0 &*& N <= 30 &*&
            thread_share(d, phase) &*&
            *phase |-> (initial_phase + N + 1) % 2;
        @*/
    {
        // Current phase is (initial_phase + N + 1) % 2, which is the X-phase.
        //@ open thread_share(d, phase);
        //@ open_mutex_fraction(b->mutex);
        //@ open barrier_inv(b, d, phase)();
        //@ assert *phase |-> ?p &*& p == (initial_phase + N + 1) % 2;
        //@ if (p == 0) open data_phase_x(d); else open data_phase_y(d);
        
        int a1 = d->x1;
        int a2 = d->x2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->y1 = a1 + 2 * a2;
        
        //@ if (p == 0) close data_phase_x(d); else close data_phase_y(d);
        //@ close barrier_inv(b, d, phase)();
        //@ close_mutex_fraction(b->mutex);
        
        {
            barrier(b);
        }
        
        // Current phase is (initial_phase + N) % 2, which is the Y-phase.
        //@ open_mutex_fraction(b->mutex);
        //@ open barrier_inv(b, d, phase)();
        //@ assert *phase |-> ?p2 &*& p2 == (initial_phase + N) % 2;
        //@ if (p2 == 0) open data_phase_y(d); else open data_phase_x(d);
           
        a1 = d->y1;
        a2 = d->y2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->x1 = a1 + 2 * a2;
        N = N + 1;
        d->i = N;
        
        //@ if (p2 == 0) close data_phase_y(d); else close data_phase_x(d);
        //@ close barrier_inv(b, d, phase)();
        //@ close_mutex_fraction(b->mutex);
        
        {
            barrier(b);
        }
        //@ close thread_share(d, phase);
    }
    {
        //@ open thread_share(d, phase);
        barrier(b);
        //@ close thread_share(d, phase);
    }
    d->i = 0;
    //@ open thread_share(d, phase);
    //@ close thread_run_post(thread1)(d, info);
}