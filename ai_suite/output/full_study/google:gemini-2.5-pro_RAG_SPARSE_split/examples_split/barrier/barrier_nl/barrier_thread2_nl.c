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
// Predicate for the physical fields of the barrier struct.
predicate barrier_fields(struct barrier *b; int n, int k, bool outgoing) =
    b->n |-> n &*&
    b->k |-> k &*&
    b->outgoing |-> outgoing;

// Predicate for the shared data fields.
predicate data_fields(struct data *d; int x1, int x2, int y1, int y2, int i) =
    d->x1 |-> x1 &*&
    d->x2 |-> x2 &*&
    d->y1 |-> y1 &*&
    d->y2 |-> y2 &*&
    d->i |-> i;

// The comprehensive invariant for the barrier's mutex.
// It includes the state of the barrier, the shared data, and a ghost 'stage' variable.
predicate barrier_inv(struct barrier *b, struct data *d; int stage, int x1, int x2, int y1, int y2, int i) =
    b->mutex |-> ?m &*&
    d->barrier |-> b &*&
    barrier_fields(b, 2, ?k, ?og) &*&
    data_fields(d, x1, x2, y1, y2, i) &*&
    // Invariants on values based on the stage.
    0 <= x1 &*& x1 <= 1000 &*&
    0 <= x2 &*& x2 <= 1000 &*&
    (stage == 1 || stage == 2 ? 0 <= y1 &*& y1 <= 4000 &*& 0 <= y2 &*& y2 <= 4000 : true) &*&
    0 <= i &*& i <= 30;

// A predicate_ctor to be used as the mutex's invariant type.
predicate_ctor barrier_mutex_inv(struct barrier *b, struct data *d)() =
    barrier_inv(b, d, ?stage, ?x1, ?x2, ?y1, ?y2, ?i);

// A helper lemma for the ghost critical sections.
typedef lemma void work_t(int stage, int x1, int x2, int y1, int y2, int i);
    requires barrier_inv(?b, ?d, stage, x1, x2, y1, y2, i);
    ensures barrier_inv(b, d, stage, ?nx1, ?nx2, ?ny1, ?ny2, ?ni);

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
    /*@ requires [?f]mutex(b->mutex, ?p) &*&
                 p == barrier_mutex_inv(?b_ghost, ?d_ghost) &*&
                 b == b_ghost;
    @*/
    /*@ ensures [f]mutex(b->mutex, p) &*&
                p == barrier_mutex_inv(b, d_ghost);
    @*/
{
    struct mutex *mutex = b->mutex;
    mutex_acquire(mutex);
    //@ open barrier_mutex_inv(b, ?d)();
    //@ open barrier_inv(b, d, ?stage, ?x1, ?x2, ?y1, ?y2, ?i);

    while (b->outgoing)
        /*@ invariant b->mutex |-> mutex &*& d->barrier |-> b &*&
                     barrier_fields(b, 2, ?k, true) &*&
                     data_fields(d, x1, x2, y1, y2, i) &*&
                     0 <= x1 &*& x1 <= 1000 &*& 0 <= x2 &*& x2 <= 1000 &*&
                     (stage == 1 || stage == 2 ? 0 <= y1 &*& y1 <= 4000 &*& 0 <= y2 &*& y2 <= 4000 : true) &*&
                     0 <= i &*& i <= 30;
        @*/
    {
        //@ int new_stage = (stage + 1) % 3;
        //@ close barrier_inv(b, d, new_stage, x1, x2, y1, y2, i);
        //@ close barrier_mutex_inv(b, d)();
        mutex_release(mutex);
        mutex_acquire(mutex);
        //@ open barrier_mutex_inv(b, d)();
        //@ open barrier_inv(b, d, new_stage, x1, x2, y1, y2, i);
        //@ stage = new_stage;
    }

    b->k++;
    if (b->k == b->n) {
        b->outgoing = true;
        b->k--;
        //@ int new_stage = (stage + 1) % 3;
        //@ close barrier_inv(b, d, new_stage, x1, x2, y1, y2, i);
        //@ close barrier_mutex_inv(b, d)();
        mutex_release(b->mutex);
    } else {
        //@ close barrier_inv(b, d, stage, x1, x2, y1, y2, i);
        //@ close barrier_mutex_inv(b, d)();
        while (!b->outgoing)
            /*@ invariant [1]mutex(mutex, barrier_mutex_inv(b, d));
            @*/
        {
            mutex_release(mutex);
            mutex_acquire(mutex);
        }
        //@ open barrier_mutex_inv(b, d)();
        //@ open barrier_inv(b, d, ?new_stage, ?nx1, ?nx2, ?ny1, ?ny2, ?ni);
        b->k--;
        if (b->k == 0) {
            b->outgoing = false;
        }
        //@ close barrier_inv(b, d, new_stage, nx1, nx2, ny1, ny2, ni);
        //@ close barrier_mutex_inv(b, d)();
        mutex_release(mutex);
    }
}


/*@
// Predicate family for thread2's precondition.
// It holds a fraction of the mutex.
predicate_family_instance thread_run_pre(thread2)(struct data *d, any info) =
    [1/2]mutex(d->barrier->mutex, barrier_mutex_inv(d->barrier, d));

// Predicate family for thread2's postcondition.
predicate_family_instance thread_run_post(thread2)(struct data *d, any info) =
    [1/2]mutex(d->barrier->mutex, barrier_mutex_inv(d->barrier, d));
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
void thread2(struct data *d) //@ : thread_run_joinable
    //@ requires thread_run_pre(thread2)(d, ?info) &*& lockset(currentThread, nil);
    //@ ensures thread_run_post(thread2)(d, info) &*& lockset(currentThread, nil);
{
    //@ open thread_run_pre(thread2)(d, info);
    struct barrier *barrier = d->barrier;
    
    barrier(barrier);
    
    int m = 0;
    while (m < 30)
        /*@ invariant [1/2]mutex(barrier->mutex, barrier_mutex_inv(barrier, d)) &*&
                      m == (m < 30 ? (barrier_mutex_inv(barrier, d)(), barrier_inv(barrier, d, ?s, ?x1,?x2,?y1,?y2,?i), i) : 30);
        @*/
    {
        // Stage 0: Update y2
        {
            /*@
            lemma void work()
                requires barrier_inv(barrier, d, 0, ?x1, ?x2, ?y1, ?y2, ?i);
                ensures barrier_inv(barrier, d, 0, x1, x2, y1, x1 + 3 * x2, i);
            {
                open barrier_inv(barrier, d, 0, x1, x2, y1, y2, i);
                d->y2 = x1 + 3 * x2;
                close data_fields(d, x1, x2, y1, x1 + 3 * x2, i);
                close barrier_inv(barrier, d, 0, x1, x2, y1, x1 + 3 * x2, i);
            }
            @*/
            //@ produce_lemma_function_pointer_chunk(work) : work_t(0, _, _, _, _, _)() { call(); };
            //@ mutex_ghost_use(barrier->mutex, work);
        }
        
        barrier(barrier);
        
        // Stage 1: Update x2
        {
            /*@
            lemma void work()
                requires barrier_inv(barrier, d, 1, ?x1, ?x2, ?y1, ?y2, ?i);
                ensures barrier_inv(barrier, d, 1, x1, y1 + 3 * y2, y1, y2, i);
            {
                open barrier_inv(barrier, d, 1, x1, x2, y1, y2, i);
                d->x2 = y1 + 3 * y2;
                close data_fields(d, x1, y1 + 3 * y2, y1, y2, i);
                close barrier_inv(barrier, d, 1, x1, y1 + 3 * y2, y1, y2, i);
            }
            @*/
            //@ produce_lemma_function_pointer_chunk(work) : work_t(1, _, _, _, _, _)() { call(); };
            //@ mutex_ghost_use(barrier->mutex, work);
        }
        
        barrier(barrier);
        
        // Stage 2: Read i
        {
            /*@
            lemma void work()
                requires barrier_inv(barrier, d, 2, ?x1, ?x2, ?y1, ?y2, ?i);
                ensures barrier_inv(barrier, d, 2, x1, x2, y1, y2, i);
            {
                open barrier_inv(barrier, d, 2, x1, x2, y1, y2, i);
                m = i;
                close barrier_inv(barrier, d, 2, x1, x2, y1, y2, i);
            }
            @*/
            //@ produce_lemma_function_pointer_chunk(work) : work_t(2, _, _, _, _, _)() { call(); };
            //@ mutex_ghost_use(barrier->mutex, work);
        }
    }
    
    barrier(barrier);
    
    //@ close thread_run_post(thread2)(d, info);
}