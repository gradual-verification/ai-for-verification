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
// Predicate for the state protected by the barrier's mutex.
// It owns the mutable fields 'k' and 'outgoing'.
predicate_ctor barrier_inv(struct barrier *b, int n)() =
    b->k |-> ?k &*&
    b->outgoing |-> ?o &*&
    0 <= k &*& k <= n;

// Predicate for a valid barrier.
// It owns the immutable field 'n', the mutex pointer, the mutex itself,
// and the malloc_block for the struct.
predicate barrier(struct barrier *b; int n) =
    b->n |-> n &*&
    b->mutex |-> ?mutex &*&
    mutex(mutex, barrier_inv(b, n)) &*&
    malloc_block_barrier(b);
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
/*@
requires n > 0;
ensures barrier(result, n) &*& result != 0;
@*/
struct barrier *create_barrier(int n)
{
    struct barrier *barrier = malloc(sizeof(struct barrier));
    if (barrier == 0) abort();
    barrier->n = n;
    barrier->k = 0;
    barrier->outgoing = false;
    
    //@ close barrier_inv(barrier, n)();
    //@ close create_mutex_ghost_arg(barrier_inv(barrier, n));
    struct mutex *mutex = create_mutex();
    
    barrier->mutex = mutex;
    
    //@ close barrier(barrier, n);
    return barrier;
}