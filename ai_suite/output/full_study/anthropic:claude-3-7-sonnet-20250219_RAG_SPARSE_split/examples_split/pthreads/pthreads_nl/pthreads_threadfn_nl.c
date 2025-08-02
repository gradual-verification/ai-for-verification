#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>

/***
 * Variable: g
 * Description:
 * A global integer shared between threads, protected by a spinlock.
 */
static int g;

/***
 * Variable: g_lock
 * Description:
 * A spinlock used to synchronize access to the shared global variable `g`.
 */
pthread_spinlock_t g_lock;

//@ predicate g_lock_invariant() = integer(&g, ?v) &*& 0 <= v &*& v <= 1024;

// TODO: make this function pass the verification
/***
 * Function: threadfn
 *
 * Description:
 * Function executed by each thread.
 * Acquires the spinlock, increments `g` if it is less than 1024, and then releases the lock.
 *
@param _unused - placeholder argument, not used.
@return NULL pointer on completion.

It requires and ensures g is within the range [0, 1024].
 */
void *threadfn(void* _unused)
//@ requires [?f]pthread_spinlock(&g_lock, ?lockId, g_lock_invariant) &*& lockset(currentThread, ?locks) &*& lock_below_top_x(lockId, locks) == true;
//@ ensures [f]pthread_spinlock(&g_lock, lockId, g_lock_invariant) &*& lockset(currentThread, locks);
{
  pthread_spin_lock(&g_lock);
  //@ open g_lock_invariant();

  if (g < 1024) { 
    //@ produce_limits(g);
    g = g + 1; 
  }

  //@ close g_lock_invariant();
  pthread_spin_unlock(&g_lock);

  return ((void *) 0);
}