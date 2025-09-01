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
// Predicate to represent the barrier's internal state
predicate_ctor barrier_inv(struct barrier *b)() = 
    b->n |-> ?n &*& 
    b->k |-> ?k &*& 
    b->outgoing |-> ?outgoing &*& 
    0 <= k &*& k <= n;

// Predicate representing a barrier
predicate barrier(struct barrier *b; int n) = 
    b->mutex |-> ?m &*& 
    mutex(m, barrier_inv(b)) &*& 
    malloc_block_barrier(b);

// Predicate for shared data
predicate shared_data(struct data *d) =
    d->x1 |-> ?x1 &*& 
    d->x2 |-> ?x2 &*& 
    d->y1 |-> ?y1 &*& 
    d->y2 |-> ?y2 &*& 
    d->i |-> ?i &*&
    0 <= x1 &*& x1 <= 1000 &*&
    0 <= x2 &*& x2 <= 1000 &*&
    0 <= y1 &*& y1 <= 1000 &*&
    0 <= y2 &*& y2 <= 1000 &*&
    malloc_block_data(d);
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
//@ requires n > 0;
//@ ensures result == 0 ? true : barrier(result, n);
{
    struct barrier *barrier = malloc(sizeof(struct barrier));
    if (barrier == 0) abort();
    barrier->n = n;
    barrier->k = 0;
    barrier->outgoing = false;
    //@ close barrier_inv(barrier)();
    //@ close create_mutex_ghost_arg(barrier_inv(barrier));
    struct mutex *mutex = create_mutex();
    barrier->mutex = mutex;
    //@ close barrier(barrier, n);
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
 * (`k`) and to handle the barrier's `outgoing` flag. Threads spin inside 
 * critical sections (by releasing and reacquiring the mutex) until the 
 * barrier state changes appropriately.
 * 
 * It requires that the barrier is incoming at the beginning, and makes sure that
 * the barrier is exiting at the end.
 */
void barrier(struct barrier *barrier)
//@ requires [?f]barrier(barrier, ?n);
//@ ensures [f]barrier(barrier, n);
{
    //@ open [f]barrier(barrier, n);
    struct mutex *mutex = barrier->mutex;
    mutex_acquire(mutex);
    //@ open barrier_inv(barrier)();

    {
        while (barrier->outgoing)
        //@ invariant barrier->n |-> n &*& barrier->k |-> ?k &*& barrier->outgoing |-> ?outgoing &*& 0 <= k &*& k <= n;
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
        //@ invariant barrier->n |-> n &*& barrier->k |-> ?k &*& barrier->outgoing |-> ?outgoing &*& 0 <= k &*& k <= n;
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
    //@ close [f]barrier(barrier, n);
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
void barrier_dispose(struct barrier *barrier)
//@ requires barrier(barrier, ?n);
//@ ensures true;
{
    //@ open barrier(barrier, n);
    mutex_dispose(barrier->mutex);
    free(barrier);
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
/*@
predicate_family_instance thread_run_data(thread1)(struct data *d) =
    d->barrier |-> ?b &*& 
    [1/3]barrier(b, 2) &*& 
    shared_data(d);
@*/

void thread1(struct data *d) //@ : thread_run
//@ requires thread_run_data(thread1)(d);
//@ ensures true;
{
    //@ open thread_run_data(thread1)(d);
    //@ open shared_data(d);
    struct barrier *b = d->barrier;
    {
        barrier(b);
    }
    int N = 0;
    while (N < 30)
    //@ invariant [1/3]barrier(b, 2) &*& d->x1 |-> ?x1 &*& d->x2 |-> ?x2 &*& d->y1 |-> ?y1 &*& d->y2 |-> ?y2 &*& d->i |-> ?i &*& 0 <= N &*& N <= 30 &*& 0 <= x1 &*& x1 <= 1000 &*& 0 <= x2 &*& x2 <= 1000 &*& 0 <= y1 &*& y1 <= 1000 &*& 0 <= y2 &*& y2 <= 1000 &*& malloc_block_data(d);
    {
        int a1 = d->x1;
        int a2 = d->x2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->y1 = a1 + 2 * a2;
        {
            barrier(b);
        }
        a1 = d->y1;
        a2 = d->y2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->x1 = a1 + 2 * a2;
        N = N + 1;
        d->i = N;
        {
            barrier(b);
        }
    }
    {
        barrier(b);
    }
    d->i = 0;
    //@ leak [1/3]barrier(b, 2);
    //@ close shared_data(d);
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
/*@
predicate_family_instance thread_run_data(thread2)(struct data *d) =
    d->barrier |-> ?b &*& 
    [1/3]barrier(b, 2) &*& 
    shared_data(d);
@*/

void thread2(struct data *d) //@ : thread_run
//@ requires thread_run_data(thread2)(d);
//@ ensures true;
{
    //@ open thread_run_data(thread2)(d);
    //@ open shared_data(d);
    struct barrier *b = d->barrier;
    {
        barrier(b);
    }
    int m = 0;
    while (m < 30)
    //@ invariant [1/3]barrier(b, 2) &*& d->x1 |-> ?x1 &*& d->x2 |-> ?x2 &*& d->y1 |-> ?y1 &*& d->y2 |-> ?y2 &*& d->i |-> ?i &*& 0 <= m &*& m <= 30 &*& 0 <= x1 &*& x1 <= 1000 &*& 0 <= x2 &*& x2 <= 1000 &*& 0 <= y1 &*& y1 <= 1000 &*& 0 <= y2 &*& y2 <= 1000 &*& malloc_block_data(d);
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
    //@ leak [1/3]barrier(b, 2);
    //@ close shared_data(d);
}


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
int main() //@ : main
//@ requires true;
//@ ensures true;
{
    struct data *d = calloc(1, sizeof(struct data));
    if (d == 0) abort();
    
    //@ close shared_data(d);
    struct barrier *barrier = create_barrier(2);
    d->barrier = barrier;

    //@ open shared_data(d);
    //@ close shared_data(d);
    //@ close thread_run_data(thread1)(d);
    struct thread *t1 = thread_start_joinable(thread1, d);

    //@ open shared_data(d);
    //@ close shared_data(d);
    //@ close thread_run_data(thread2)(d);
    struct thread *t2 = thread_start_joinable(thread2, d);
    
    thread_join(t1);
    thread_join(t2);
    
    //@ open shared_data(d);
    barrier_dispose(d->barrier);
    free(d);
    return 0;
}