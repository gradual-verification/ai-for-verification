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
// N: main loop counter (0-30). phase: sub-computation step (0-2).
// phase 0: y values are computed.
// phase 1: x values are computed.
// phase 2: i is updated.
predicate_ctor barrier_inv(struct barrier *b, struct data *d, int N, int phase)() =
    b->n |-> 2 &*& b->k |-> ?k &*& b->outgoing |-> ?outgoing &*&
    d->barrier |-> b &*&
    0 <= k &*& k <= 2 &*& (k == 2 ? outgoing == false : true) &*&
    0 <= N &*& N <= 30 &*& 0 <= phase &*& phase <= 2 &*&
    (
        k == 0 && !outgoing ?
            d->x1 |-> 0 &*& d->x2 |-> 0 &*& d->y1 |-> 0 &*& d->y2 |-> 0 &*&
            d->i |-> (phase == 2 ? N + 1 : N)
        : k == 1 && !outgoing ?
            (
                phase == 0 ?
                    [1/2]d->x1 |-> 0 &*& [1/2]d->x2 |-> 0 &*&
                    d->y1 |-> 0 &*& d->y2 |-> _ &*& [1/2]d->i |-> N
                : phase == 1 ?
                    [1/2]d->y1 |-> 0 &*& [1/2]d->y2 |-> 0 &*&
                    d->x1 |-> 0 &*& d->x2 |-> _ &*& [1/2]d->i |-> N
                : d->x1 |-> 0 &*& d->x2 |-> 0 &*& d->y1 |-> 0 &*& d->y2 |-> 0 &*& d->i |-> N + 1
            )
        : k == 1 && outgoing ?
            (
                phase == 0 ?
                    d->x1 |-> _ &*& d->x2 |-> _ &*&
                    [1/2]d->y1 |-> 0 &*& [1/2]d->y2 |-> 0 &*& [1/2]d->i |-> N
                : phase == 1 ?
                    [1/2]d->x1 |-> 0 &*& [1/2]d->x2 |-> 0 &*&
                    [1/2]d->y1 |-> 0 &*& [1/2]d->y2 |-> 0 &*& d->i |-> _
                : [1/2]d->x1 |-> 0 &*& [1/2]d->x2 |-> 0 &*&
                  [1/2]d->y1 |-> 0 &*& [1/2]d->y2 |-> 0 &*& [1/2]d->i |-> N + 1
            )
        : false
    );

predicate barrier_object(struct barrier *b, struct data *d, int N, int phase) =
    b->mutex |-> ?m &*& malloc_block_barrier(b) &*&
    mutex(m, barrier_inv(b, d, N, phase));

// Permissions for thread 1 before a barrier call
predicate t1_perms(struct data *d, int N, int phase) =
    d->barrier |-> ?b &*& [1/2]barrier_object(b, d, N, phase) &*&
    (
        phase == 0 ?
            [1/2]d->x1 |-> 0 &*& [1/2]d->x2 |-> 0 &*& d->y1 |-> _ &*& [1/2]d->i |-> N
        : phase == 1 ?
            d->x1 |-> _ &*& [1/2]d->y1 |-> 0 &*& [1/2]d->y2 |-> 0 &*& d->i |-> _
        :
            [1/2]d->x1 |-> 0 &*& [1/2]d->x2 |-> 0 &*&
            [1/2]d->y1 |-> 0 &*& [1/2]d->y2 |-> 0 &*& d->i |-> N
    );

// Permissions for thread 2 before a barrier call
predicate t2_perms(struct data *d, int N, int phase) =
    d->barrier |-> ?b &*& [1/2]barrier_object(b, d, N, phase) &*&
    (
        phase == 0 ?
            [1/2]d->x1 |-> 0 &*& [1/2]d->x2 |-> 0 &*& d->y2 |-> _ &*& [1/2]d->i |-> N
        : phase == 1 ?
            d->x2 |-> _ &*& [1/2]d->y1 |-> 0 &*& [1/2]d->y2 |-> 0 &*& [1/2]d->i |-> N
        :
            [1/2]d->x1 |-> 0 &*& [1/2]d->x2 |-> 0 &*&
            [1/2]d->y1 |-> 0 &*& [1/2]d->y2 |-> 0 &*& [1/2]d->i |-> N + 1
    );

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
    //@ requires n == 2 &*& barrier_inv(?b, ?d, ?N, ?phase)();
    //@ ensures barrier_object(result, d, N, phase) &*& result->n |-> n;
{
    struct barrier *barrier = malloc(sizeof(struct barrier));
    if (barrier == 0) abort();
    barrier->n = n;
    barrier->k = 0;
    barrier->outgoing = false;
    //@ close barrier_inv(barrier, d, N, phase)();
    //@ close create_mutex_ghost_arg(barrier_inv(barrier, d, N, phase));
    struct mutex *mutex = create_mutex();
    barrier->mutex = mutex;
    //@ close barrier_object(barrier, d, N, phase);
    return barrier;
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
    /*@ requires
            [?f]barrier_object(b, ?d, ?N, ?phase) &*&
            (
                is_thread_run_joinable(thread1, d) ?
                    t1_perms(d, N, phase)
                :
                    t2_perms(d, N, phase)
            );
    @*/
    /*@ ensures
            [f]barrier_object(b, d, phase == 2 ? N + 1 : N, (phase + 1) % 3) &*&
            (
                is_thread_run_joinable(thread1, d) ?
                    t1_perms(d, phase == 2 ? N + 1 : N, (phase + 1) % 3)
                :
                    t2_perms(d, phase == 2 ? N + 1 : N, (phase + 1) % 3)
            );
    @*/
{
    //@ open barrier_object(b, d, N, phase);
    struct mutex *mutex = b->mutex;
    mutex_acquire(mutex);
    //@ open barrier_inv(b, d, N, phase)();

    {
        while (b->outgoing)
            //@ invariant mutex_held(mutex, barrier_inv(b, d, N, phase), currentThread, f) &*& b->outgoing |-> true &*& b->k |-> ?k &*& 0 <= k &*& k < 2 &*& d->barrier |-> b;
        {
            //@ close barrier_inv(b, d, N, phase)();
            mutex_release(mutex);
            mutex_acquire(mutex);
            //@ open barrier_inv(b, d, N, phase)();
        }
    }
    
    //@ assert b->k |-> ?k_pre &*& b->outgoing |-> false;
    //@ if (k_pre == 0) { open t1_perms(d, N, phase); open t2_perms(d, N, phase); }
    //@ else { assert k_pre == 1; }
    
    b->k++;
    if (b->k == b->n) {
        b->outgoing = true;
        b->k--;
        //@ int next_N = phase == 2 ? N + 1 : N;
        //@ int next_phase = (phase + 1) % 3;
        //@ close barrier_inv(b, d, next_N, next_phase)();
        mutex_release(b->mutex);
    } else {
        while (!b->outgoing)
            //@ invariant mutex_held(mutex, barrier_inv(b, d, N, phase), currentThread, f) &*& b->outgoing |-> false &*& b->k |-> 1 &*& d->barrier |-> b;
        {
            //@ close barrier_inv(b, d, N, phase)();
            mutex_release(mutex);
            mutex_acquire(mutex);
            //@ open barrier_inv(b, d, N, phase)();
        }

        b->k--;
        if (b->k == 0) {
            b->outgoing = false;
        }
        //@ int next_N = phase == 2 ? N + 1 : N;
        //@ int next_phase = (phase + 1) % 3;
        //@ close barrier_inv(b, d, next_N, next_phase)();
        mutex_release(mutex);
    }
    //@ close [f]barrier_object(b, d, phase == 2 ? N + 1 : N, (phase + 1) % 3);
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
    //@ requires barrier_object(b, ?d, ?N, ?phase);
    //@ ensures d->barrier |-> b &*& d->x1 |-> 0 &*& d->x2 |-> 0 &*& d->y1 |-> 0 &*& d->y2 |-> 0 &*& d->i |-> (phase == 2 ? N + 1 : N);
{
    //@ open barrier_object(b, d, N, phase);
    mutex_dispose(b->mutex);
    //@ open barrier_inv(b, d, N, phase)();
    free(b);
}

/*@
predicate_family_instance thread_run_pre(thread1)(void *data, any info) =
    t1_perms(data, 0, 0);
predicate_family_instance thread_run_post(thread1)(void *data, any info) =
    t1_perms(data, 0, 1);

predicate_family_instance thread_run_pre(thread2)(void *data, any info) =
    t2_perms(data, 0, 0);
predicate_family_instance thread_run_post(thread2)(void *data, any info) =
    t2_perms(data, 0, 1);
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
void thread1(struct data *d) //@ : thread_run_joinable
    //@ requires thread_run_pre(thread1)(d, _);
    //@ ensures thread_run_post(thread1)(d, _);
{
    //@ open t1_perms(d, 0, 0);
    struct barrier *b = d->barrier;
    {
        barrier(b);
    }
    int N = 0;
    while (N < 30)
        /*@ invariant 0 <= N &*& N <= 30 &*&
                (
                    N == 30 ?
                        t1_perms(d, 30, 0)
                    :
                        t1_perms(d, N, 0)
                );
        @*/
    {
        //@ open t1_perms(d, N, 0);
        int a1 = d->x1;
        int a2 = d->x2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->y1 = a1 + 2 * a2;
        //@ close t1_perms(d, N, 0);
        {
            barrier(b);
        }
        //@ open t1_perms(d, N, 1);
        a1 = d->y1;
        a2 = d->y2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->x1 = a1 + 2 * a2;
        //@ close t1_perms(d, N, 1);
        {
            barrier(b);
        }
        //@ open t1_perms(d, N, 2);
        N = N + 1;
        d->i = N;
        //@ close t1_perms(d, N - 1, 2);
        {
            barrier(b);
        }
    }
    {
        barrier(b);
    }
    //@ open t1_perms(d, 30, 1);
    d->i = 0;
    //@ close t1_perms(d, 0, 1);
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
void thread2(struct data *d) //@ : thread_run_joinable
    //@ requires thread_run_pre(thread2)(d, _);
    //@ ensures thread_run_post(thread2)(d, _);
{
    //@ open t2_perms(d, 0, 0);
    struct barrier *b = d->barrier;
    {
        barrier(b);
    }
    int m = 0;
    while (m < 30)
        /*@ invariant 0 <= m &*& m <= 30 &*&
                (
                    m == 30 ?
                        t2_perms(d, 30, 0)
                    :
                        t2_perms(d, m, 0)
                );
        @*/
    {
        //@ open t2_perms(d, m, 0);
        int a1 = d->x1;
        int a2 = d->x2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->y2 = a1 + 3 * a2;
        //@ close t2_perms(d, m, 0);
        {
            barrier(b);
        }
        //@ open t2_perms(d, m, 1);
        a1 = d->y1;
        a2 = d->y2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->x2 = a1 + 3 * a2;
        //@ close t2_perms(d, m, 1);
        {
            barrier(b);
        }
        //@ open t2_perms(d, m, 2);
        m = d->i;
        //@ close t2_perms(d, m, 2);
        {
            barrier(b);
        }
    }
    {
        barrier(b);
    }
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
    
    //@ close barrier_inv(0, d, 0, 0)();
    struct barrier *barrier = create_barrier(2);
    d->barrier = barrier;

    //@ open barrier_object(barrier, d, 0, 0);
    //@ close t1_perms(d, 0, 0);
    //@ close t2_perms(d, 0, 0);
    //@ close thread_run_pre(thread1)(d, unit);
    struct thread *t1 = thread_start_joinable(thread1, d);
    //@ close thread_run_pre(thread2)(d, unit);
    struct thread *t2 = thread_start_joinable(thread2, d);
    
    thread_join(t1);
    thread_join(t2);
    
    //@ open t1_perms(d, 0, 1);
    //@ open t2_perms(d, 0, 1);
    //@ open barrier_object(barrier, d, 0, 1);
    //@ assert barrier_inv(barrier, d, 0, 1)();
    
    barrier_dispose(d->barrier);
  
    free(d);
    return 0;
}