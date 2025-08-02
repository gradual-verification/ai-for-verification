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
// Define a predicate for the barrier's internal state
predicate barrier_state(struct barrier *barrier, int n, int k, bool outgoing) =
    barrier->n |-> n &*&
    barrier->k |-> k &*&
    barrier->outgoing |-> outgoing &*&
    n > 0 &*& 0 <= k &*& k <= n;

// Define a predicate for the barrier itself
predicate barrier(struct barrier *barrier; int n) =
    barrier->mutex |-> ?mutex &*&
    mutex(mutex, barrier_state(barrier, n, ?k, ?outgoing)) &*&
    malloc_block_barrier(barrier);
@*/

// TODO: make this function pass the verification
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
    
    //@ close barrier_state(barrier, n, 0, false);
    //@ close create_mutex_ghost_arg(barrier_state(barrier, n, 0, false));
    struct mutex *mutex = create_mutex();
    barrier->mutex = mutex;
    
    //@ close barrier(barrier, n);
    return barrier;
}

/*@
// Define a predicate for the wait operation
predicate barrier_wait(struct barrier *barrier, int n) =
    [1/2]barrier(barrier, n);
@*/

/*@
// Helper lemma to prove that k is within bounds
lemma void barrier_k_bounds(int k, int n)
    requires 0 <= k &*& k <= n;
    ensures 0 <= k + 1 &*& k + 1 <= n + 1;
{
}
@*/

/***
 * Description:
 * Causes the calling thread to wait at the barrier until all `n` threads have arrived.
 *
 * @param barrier - The barrier to wait on.
 *
 * The function increments the counter of arrived threads. If this thread is the last
 * to arrive, it resets the counter and changes the barrier state to "outgoing".
 * Otherwise, it waits until all threads have arrived and the state is "outgoing".
 */
void barrier_wait(struct barrier *barrier)
//@ requires [?f]barrier(barrier, ?n) &*& 0 < f &*& f <= 1;
//@ ensures [f]barrier(barrier, n);
{
    //@ open [f]barrier(barrier, n);
    struct mutex *mutex = barrier->mutex;
    
    mutex_acquire(mutex);
    //@ open barrier_state(barrier, n, ?k, ?outgoing);
    
    int k = barrier->k;
    barrier->k = k + 1;
    
    if (k + 1 == barrier->n) {
        // Last thread to arrive
        barrier->outgoing = true;
        //@ close barrier_state(barrier, n, k + 1, true);
    } else {
        // Not the last thread, wait for others
        //@ close barrier_state(barrier, n, k + 1, outgoing);
        while (!barrier->outgoing) {
            mutex_release(mutex);
            //@ close [f]barrier(barrier, n);
            
            // Yield to other threads
            mutex_acquire(mutex);
            //@ open barrier_state(barrier, n, ?k2, ?outgoing2);
            //@ close barrier_state(barrier, n, k2, outgoing2);
        }
    }
    
    // Decrement counter for outgoing threads
    k = barrier->k;
    barrier->k = k - 1;
    
    if (k - 1 == 0) {
        // Last thread to leave
        barrier->outgoing = false;
        //@ close barrier_state(barrier, n, 0, false);
    } else {
        //@ close barrier_state(barrier, n, k - 1, true);
    }
    
    mutex_release(mutex);
    //@ close [f]barrier(barrier, n);
}

/***
 * Description:
 * Frees all resources associated with the barrier.
 *
 * @param barrier - The barrier to destroy.
 *
 * The function disposes of the mutex and frees the memory allocated for the barrier.
 */
void barrier_destroy(struct barrier *barrier)
//@ requires barrier(barrier, ?n);
//@ ensures true;
{
    //@ open barrier(barrier, n);
    mutex_dispose(barrier->mutex);
    //@ open barrier_state(barrier, n, ?k, ?outgoing);
    free(barrier);
}

int main() 
//@ requires true;
//@ ensures true;
{
    struct barrier *b = create_barrier(2);
    if (b == 0) abort();
    
    // Use the barrier
    barrier_wait(b);
    
    // Clean up
    barrier_destroy(b);
    
    return 0;
}