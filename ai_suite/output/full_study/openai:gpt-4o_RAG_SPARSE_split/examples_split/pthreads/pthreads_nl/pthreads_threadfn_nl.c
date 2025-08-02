#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>

//@ #include "prelude.h"

/***
 * Variable: g
 * Description:
 * A global integer shared between threads, protected by a spinlock.
 */
//@ predicate g_invariant() = integer(&g, ?value) &*& 0 <= value &*& value <= 1024;
static int g;

/***
 * Variable: g_lock
 * Description:
 * A spinlock used to synchronize access to the shared global variable `g`.
 */
//@ predicate g_lock_invariant() = pthread_spinlock(&g_lock, ?lockId, g_invariant);
pthread_spinlock_t g_lock;

// TODO: make this function pass the verification
/***
 * Function: threadfn
 *
 * Description:
 * Function executed by each thread.
 * Acquires the spinlock, increments `g` if it is less than 1024, and then releases the lock.
 *
 * @param _unused - placeholder argument, not used.
 * @return NULL pointer on completion.
 *
 * It requires and ensures g is within the range [0, 1024].
 */
//@ predicate_family_instance pthread_run_pre(threadfn)(void *data, any info) = g_lock_invariant();
//@ predicate_family_instance pthread_run_post(threadfn)(void *data, any info) = g_lock_invariant();

void *threadfn(void* _unused)
    //@ requires pthread_run_pre(threadfn)(_unused, ?info);
    //@ ensures pthread_run_post(threadfn)(_unused, info);
{
    pthread_spin_lock(&g_lock);
    //@ open g_invariant();
    if (g < 1024) {
        g = g + 1;
    }
    //@ close g_invariant();
    pthread_spin_unlock(&g_lock);
    return ((void *) 0);
}