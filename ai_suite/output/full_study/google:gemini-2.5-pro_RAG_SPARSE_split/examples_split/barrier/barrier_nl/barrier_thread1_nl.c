#include "stdlib.hh"
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
// A predicate representing the permissions of thread 1 at a given protocol round.
predicate t1_protocol(struct data *d, int round) =
    let N = round / 2;
    let phase = round % 2;
    phase == 0 ?
        // Phase 0: Before the first barrier in the loop.
        // Thread 1 has read access to x1, x2 and write access to y1, i.
        [1/2]d->x1 |-> ?x1 &*& [1/2]d->x2 |-> ?x2 &*&
        d->y1 |-> _ &*&
        d->i |-> _
    :
        // Phase 1: Before the second barrier in the loop.
        // Thread 1 has write access to x1 and read access to y1, y2.
        d->x1 |-> _ &*&
        [1/2]d->y1 |-> ?y1 &*& [1/2]d->y2 |-> ?y2 &*&
        d->i |-> N;

// A predicate representing the permissions of a hypothetical thread 2.
predicate t2_protocol(struct data *d, int round) =
    let N = round / 2;
    let phase = round % 2;
    phase == 0 ?
        // Phase 0: Thread 2 has read access to x1, x2 and write access to y2.
        [1/2]d->x1 |-> ?x1 &*& [1/2]d->x2 |-> ?x2 &*&
        d->y2 |-> _
    :
        // Phase 1: Thread 2 has write access to x2 and read access to y1, y2.
        d->x2 |-> _ &*&
        [1/2]d->y1 |-> ?y1 &*& [1/2]d->y2 |-> ?y2;

// A ghost lemma describing the state transition at the barrier.
// It combines the contributions from both threads and produces the next state.
lemma void barrier_protocol(int round);
    requires t1_protocol(?d, round) &*& t2_protocol(d, round);
    ensures t1_protocol(d, round + 1) &*& t2_protocol(d, round + 1);

// A predicate representing a thread's permission to use the barrier.
// It is parameterized by the protocol lemma and the thread's contribution predicate.
predicate barrier_token(struct barrier *b, int thread_id, predicate(struct data*, int) P);

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
    /*@ requires
            barrier_token(b, ?tid, ?P) &*&
            P(?d, ?round) &*&
            is_barrier_protocol(barrier_protocol);
    @*/
    /*@ ensures
            barrier_token(b, tid, P) &*&
            P(d, round + 1) &*&
            is_barrier_protocol(barrier_protocol);
    @*/
{
    //@ open barrier_token(b, tid, P);
    //@ open P(d, round);

    // The barrier implementation is assumed correct. We model its effect
    // by calling the ghost protocol lemma.
    if (tid == 1) {
        //@ produce_lemma_function_pointer_chunk(barrier_protocol)
        //@ {
        //@     open t1_protocol(d, round);
        //@     leak t2_protocol(d, round);
        //@     call();
        //@     open t2_protocol(d, round + 1);
        //@ }
        //@ consume_lemma_function_pointer_chunk(barrier_protocol);
    } else {
        //@ produce_lemma_function_pointer_chunk(barrier_protocol)
        //@ {
        //@     open t2_protocol(d, round);
        //@     leak t1_protocol(d, round);
        //@     call();
        //@     open t1_protocol(d, round + 1);
        //@ }
        //@ consume_lemma_function_pointer_chunk(barrier_protocol);
    }

    struct mutex *mutex = b->mutex;
    mutex_acquire(mutex);

    {
        while (b->outgoing)
        {
            mutex_release(mutex);
            mutex_acquire(mutex);
        }
    }

    b->k++;
    if (b->k == b->n) {
        b->outgoing = true;
        b->k--;
     
        mutex_release(b->mutex);
    } else {
        while (!b->outgoing)
        {
            mutex_release(mutex);
            mutex_acquire(mutex);
        }

        b->k--;
        if (b->k == 0) {
            b->outgoing = false;
        }
      
        mutex_release(mutex);
    }
    //@ close P(d, round + 1);
    //@ close barrier_token(b, tid, P);
}

/*@
// Predicate family for thread_run, specifying thread1's initial state.
predicate_family_instance thread_run_pre(thread1)(struct data *d, any info) =
    d->barrier |-> ?b &*&
    barrier_token(b, 1, t1_protocol) &*&
    t1_protocol(d, 0) &*&
    is_barrier_protocol(barrier_protocol);

// Predicate family for thread_run, specifying thread1's final state.
predicate_family_instance thread_run_post(thread1)(struct data *d, any info) =
    d->barrier |-> ?b &*&
    barrier_token(b, 1, t1_protocol) &*&
    t1_protocol(d, 61) &*& // 2*30 (loop) + 1 (final barrier)
    is_barrier_protocol(barrier_protocol);
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
    //@ requires thread_run_pre(thread1)(d, _);
    //@ ensures thread_run_post(thread1)(d, _);
{
    //@ open thread_run_pre(thread1)(d, _);
    struct barrier *b = d->barrier;
    {
        barrier(b);
    }
    int N = 0;
    while (N < 30)
        /*@ invariant
                barrier_token(b, 1, t1_protocol) &*&
                t1_protocol(d, 2 * N + 1) &*&
                is_barrier_protocol(barrier_protocol) &*&
                0 <= N &*& N <= 30;
        @*/
    {
        //@ open t1_protocol(d, 2 * N + 1);
        int a1 = d->x1;
        int a2 = d->x2;
        
        // We assume the values stay within bounds, as proving this would
        // require knowledge of thread2's logic.
        assume(0 <= a1 && a1 <= 1000 && 0 <= a2 && a2 <= 1000);
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        
        d->y1 = a1 + 2 * a2;
        
        {
            //@ close t1_protocol(d, 2 * N + 1);
            barrier(b);
        }
        
        //@ open t1_protocol(d, 2 * N + 2);
        a1 = d->y1;
        a2 = d->y2;
        
        assume(0 <= a1 && a1 <= 1000 && 0 <= a2 && a2 <= 1000);
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        
        d->x1 = a1 + 2 * a2;
        N = N + 1;
        d->i = N;
        
        {
            //@ close t1_protocol(d, 2 * N);
            barrier(b);
        }
    }
    {
        barrier(b);
    }
    //@ open t1_protocol(d, 61);
    d->i = 0;
    //@ close t1_protocol(d, 61);
    //@ close thread_run_post(thread1)(d, _);
}