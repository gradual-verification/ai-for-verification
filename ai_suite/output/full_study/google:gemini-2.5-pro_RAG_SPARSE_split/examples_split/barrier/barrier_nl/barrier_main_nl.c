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
    //@ box box_id;
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
// Predicate for the shared data invariant.
// 'phase' tracks the computation stage, 'N' is the loop counter.
predicate data_inv(struct data *d, int phase, int N) =
    d->x1 |-> 0 &*& d->x2 |-> 0 &*&
    d->y1 |-> 0 &*& d->y2 |-> 0 &*&
    d->i |-> N &*&
    0 <= N &*& N <= 30 &*&
    0 <= phase &*& phase <= 2;

// Box class to model the barrier's state machine.
box_class barrier_box(struct barrier *b, int n, struct data *d) {
    // Physical state of the barrier
    invariant b->k |-> ?k &*& b->outgoing |-> ?outgoing &*&
    // Ghost state
              b->phase |-> ?phase &*& b->N |-> ?N &*&
    // Invariant linking physical and ghost state
              (outgoing ? 0 < k && k <= n : 0 <= k && k < n) &*&
    // The shared data is held by the box only when the barrier is idle.
              (k == 0 && !outgoing ? data_inv(d, phase, N) : true);

    // Action for a thread arriving at the barrier.
    action arrive(int thread_id);
        requires true;
        ensures k == old_k + 1 && outgoing == old_outgoing &&
                (k < n ?
                    phase == old_phase && N == old_N
                : // Last thread to arrive advances the phase.
                    phase == (old_phase + 1) % 3 &&
                    N == (old_phase == 2 ? old_N + 1 : old_N)
                );

    // Action for a thread leaving the barrier.
    action leave(int thread_id);
        requires true;
        ensures k == old_k - 1 &&
                (k > 0 ? outgoing == old_outgoing : outgoing == false) &&
                phase == old_phase && N == old_N;

    // Handle for a thread, proving its participation.
    handle_predicate barrier_handle(int thread_id) {
        invariant true;
        preserved_by arrive(thread_id) {}
        preserved_by leave(thread_id) {}
    }
}

// Predicate for the barrier object itself.
predicate barrier(struct barrier *b, int n, struct data *d) =
    b->mutex |-> ?m &*&
    b->box_id |-> ?box_id &*&
    malloc_block_barrier(b) &*&
    mutex(m, barrier_box(box_id, b, n, d));
@*/

/***
 * Description:
 * Creates and initializes a new barrier intended for `n` threads.
 *
 * @param n - The number of threads to synchronize with this barrier.
 * @returns A pointer to a newly allocated and initialized `struct barrier`.
 *
 * The function allocates memory for the barrier, sets all fields to default
 * values, and creates a mutex to protect updates to the barrier.
 */
struct barrier *create_barrier(int n)
    //@ requires n > 0 &*& exists<struct data *>(?d) &*& data_inv(d, 0, 0);
    //@ ensures barrier(result, n, d) &*& result->box_id |-> ?box_id &*& foreach(range(0, n), (barrier_handle)(box_id));
{
    struct barrier *b = malloc(sizeof(struct barrier));
    if (b == 0) abort();
    b->n = n;
    b->k = 0;
    b->outgoing = false;
    //@ b->phase = 0;
    //@ b->N = 0;
    //@ create_box box_id = barrier_box(b, n, d);
    //@ b->box_id = box_id;
    //@ close barrier_box(box_id, b, n, d);
    struct mutex *mutex = create_mutex();
    b->mutex = mutex;
    //@ close barrier(b, n, d);
    //@ foreach_create_handle_from_zero(n, barrier_box_handle(box_id));
    return b;
}


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
    //@ requires [?f]barrier(b, ?n, ?d) &*& barrier_handle(?box_id, ?id) &*& b->box_id |-> box_id &*& (f > 0);
    //@ ensures [f]barrier(b, n, d) &*& barrier_handle(box_id, id);
{
    //@ open barrier(b, n, d);
    struct mutex *mutex = b->mutex;
    mutex_acquire(mutex);
    //@ open barrier_box(box_id, b, n, d);

    while (b->outgoing)
        //@ invariant mutex_held(mutex, barrier_box(box_id, b, n, d), currentThread, f) &*& b->k |-> ?k &*& b->outgoing |-> true &*& k > 0 &*& k <= n &*& b->n |-> n &*& b->phase |-> _ &*& b->N |-> _;
    {
        //@ close barrier_box(box_id, b, n, d);
        mutex_release(mutex);
        mutex_acquire(mutex);
        //@ open barrier_box(box_id, b, n, d);
    }

    //@ assert b->k |-> ?k_old &*& k_old < n;
    //@ assert b->phase |-> ?phase_old &*& b->N |-> ?N_old;
    //@ if (k_old == 0) open data_inv(d, phase_old, N_old);
    /*@
    consuming_box_predicate barrier_box(box_id, b, n, d)
    consuming_handle_predicate barrier_handle(id)
    perform_action arrive(id) {
    @*/
    b->k++;
    /*@
    }
    producing_box_predicate barrier_box(b, n, d)
    producing_handle_predicate barrier_handle(id);
    @*/
    //@ assert b->k |-> ?k_new &*& k_new == k_old + 1;
    //@ if (k_new < n) { close data_inv(d, phase_old, N_old); } else { assert b->phase |-> (phase_old + 1) % 3; }

    if (b->k == b->n) {
        b->outgoing = true;
        /*@
        consuming_box_predicate barrier_box(box_id, b, n, d)
        consuming_handle_predicate barrier_handle(id)
        perform_action leave(id) {
        @*/
        b->k--;
        /*@
        }
        producing_box_predicate barrier_box(b, n, d)
        producing_handle_predicate barrier_handle(id);
        @*/
        //@ close barrier_box(box_id, b, n, d);
        mutex_release(b->mutex);
    } else {
        //@ close barrier_box(box_id, b, n, d);
        while (!b->outgoing)
            //@ invariant mutex_held(mutex, barrier_box(box_id, b, n, d), currentThread, f) &*& b->k |-> ?k &*& b->outgoing |-> false &*& k > 0 &*& k < n &*& b->n |-> n &*& b->phase |-> _ &*& b->N |-> _;
        {
            mutex_release(mutex);
            mutex_acquire(mutex);
            //@ open barrier_box(box_id, b, n, d);
        }
        
        /*@
        consuming_box_predicate barrier_box(box_id, b, n, d)
        consuming_handle_predicate barrier_handle(id)
        perform_action leave(id) {
        @*/
        b->k--;
        /*@
        }
        producing_box_predicate barrier_box(b, n, d)
        producing_handle_predicate barrier_handle(id);
        @*/

        if (b->k == 0) {
            b->outgoing = false;
            //@ assert b->phase |-> ?phase;
            //@ assert b->N |-> ?N;
            //@ close data_inv(d, phase, N);
        }
        //@ close barrier_box(box_id, b, n, d);
        mutex_release(mutex);
    }
    //@ close [f]barrier(b, n, d);
}


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
void barrier_dispose(struct barrier *b)
    //@ requires barrier(b, ?n, ?d) &*& b->box_id |-> ?box_id &*& foreach(range(0, n), (barrier_handle)(box_id)) &*& data_inv(d, _, _);
    //@ ensures malloc_block_data(d);
{
    //@ open barrier(b, n, d);
    mutex_dispose(b->mutex);
    //@ open barrier_box(b->box_id, b, n, d);
    //@ dispose_box barrier_box(b->box_id, b, n, d);
    //@ foreach_dispose((barrier_handle)(b->box_id));
    free(b);
}

/*@
// Predicate families for thread contracts
predicate_family_instance thread_run_pre(thread1)(void *data, pair<int, box> info) =
    [1/2]data_pred(data) &*&
    switch(info) { case pair(id, box_id): return barrier_handle(box_id, id); };

predicate_family_instance thread_run_post(thread1)(void *data, pair<int, box> info) =
    [1/2]data_pred(data) &*&
    switch(info) { case pair(id, box_id): return barrier_handle(box_id, id); };

predicate_family_instance thread_run_pre(thread2)(void *data, pair<int, box> info) =
    [1/2]data_pred(data) &*&
    switch(info) { case pair(id, box_id): return barrier_handle(box_id, id); };

predicate_family_instance thread_run_post(thread2)(void *data, pair<int, box> info) =
    [1/2]data_pred(data) &*&
    switch(info) { case pair(id, box_id): return barrier_handle(box_id, id); };

predicate data_pred(struct data *d) =
    d->barrier |-> ?b &*& [1/2]barrier(b, 2, d) &*& b->box_id |-> _;
@*/

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
    //@ open data_pred(d);
    struct barrier *b = d->barrier;
    
    barrier(b);

    int N = 0;
    while (N < 30)
        //@ invariant [1/4]barrier(b, 2, d) &*& barrier_handle(b->box_id, fst(info)) &*& d->barrier |-> b;
    {
        // Phase 0: compute y1
        int a1 = d->x1;
        int a2 = d->x2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->y1 = a1 + 2 * a2;
        
        barrier(b);
        
        // Phase 1: compute x1
        a1 = d->y1;
        a2 = d->y2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->x1 = a1 + 2 * a2;
        N = N + 1;
        d->i = N;
        
        barrier(b);
        
        // Phase 2: loop back
        barrier(b);
    }
    
    barrier(b);
    d->i = 0;
    //@ close data_pred(d);
    //@ close thread_run_post(thread1)(d, info);
}


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
    //@ requires thread_run_pre(thread2)(d, ?info);
    //@ ensures thread_run_post(thread2)(d, info);
{
    //@ open thread_run_pre(thread2)(d, info);
    //@ open data_pred(d);
    struct barrier *b = d->barrier;
    
    barrier(b);
    
    int m = 0;
    while (m < 30)
        //@ invariant [1/4]barrier(b, 2, d) &*& barrier_handle(b->box_id, fst(info)) &*& d->barrier |-> b;
    {
        // Phase 0: compute y2
        int a1 = d->x1;
        int a2 = d->x2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->y2 = a1 + 3 * a2;
        
        barrier(b);
        
        // Phase 1: compute x2
        a1 = d->y1;
        a2 = d->y2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->x2 = a1 + 3 * a2;
        
        barrier(b);
        
        // Phase 2: loop back
        m = d->i;
        barrier(b);
    }
    
    barrier(b);
    //@ close data_pred(d);
    //@ close thread_run_post(thread2)(d, info);
}


// TODO: make this function pass the verification
/***
 * Description:
 * The main function sets up the shared data and barrier, starts two threads
 * (`thread1` and `thread2`) to demonstrate coordination via the barrier, and 
 * then waits for both to finish. Finally, it disposes of the barrier and 
 * frees the shared data.
 *
 * @returns 0 on successful completion of both threads.
 *
 * If any allocation fails, the process calls `abort()`.
 */
int main()
    //@ requires true;
    //@ ensures true;
{
    struct data *d = calloc(1, sizeof(struct data));
    if (d == 0) abort();
    //@ close data_inv(d, 0, 0);
    
    struct barrier *b = create_barrier(2);
    d->barrier = b;
    //@ box box_id = b->box_id;
    //@ open foreach(cons(0, cons(1, nil)), (barrier_handle)(box_id));
    //@ assert barrier_handle(box_id, 0) &*& foreach(cons(1, nil), (barrier_handle)(box_id));
    //@ open foreach(cons(1, nil), (barrier_handle)(box_id));
    //@ assert barrier_handle(box_id, 1) &*& foreach(nil, (barrier_handle)(box_id));
    //@ open foreach(nil, (barrier_handle)(box_id));

    //@ close data_pred(d);
    //@ close data_pred(d);
    //@ close thread_run_pre(thread1)(d, pair(0, box_id));
    struct thread *t1 = thread_start_joinable(thread1, d);
    //@ close thread_run_pre(thread2)(d, pair(1, box_id));
    struct thread *t2 = thread_start_joinable(thread2, d);
    
    thread_join(t1);
    //@ open thread_run_post(thread1)(d, pair(0, box_id));
    thread_join(t2);
    //@ open thread_run_post(thread2)(d, pair(1, box_id));
    
    //@ open data_pred(d);
    //@ open data_pred(d);
    //@ close foreach(cons(1, nil), (barrier_handle)(box_id));
    //@ close foreach(cons(0, cons(1, nil)), (barrier_handle)(box_id));
    barrier_dispose(d->barrier);
  
    free(d);
    return 0;
}