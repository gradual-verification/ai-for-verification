#include "stdlib.h"
#include "threading.h"

//@ predicate barrier(struct barrier *barrier, int n) =
//@     barrier->n |-> n &*& barrier->k |-> 0 &*& barrier->outgoing |-> false &*&
//@     barrier->mutex |-> ?mutex &*& mutex(mutex, barrier(barrier, n));

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
//@ requires n > 0;
//@ ensures result != 0 ? barrier(result, n) : true;
struct barrier *create_barrier(int n)
{
    struct barrier *barrier = malloc(sizeof(struct barrier));
    if (barrier == 0) abort();
    barrier->n = n;
    barrier->k = 0;
    barrier->outgoing = false;
    //@ close create_mutex_ghost_arg(barrier(barrier, n));
    struct mutex *mutex = create_mutex();
    barrier->mutex = mutex;
    //@ close barrier(barrier, n);
    return barrier;
}