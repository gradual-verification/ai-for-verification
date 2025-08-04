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


/*@
// Predicate describing the shared resource `g` and its invariant.
// This invariant ensures that `g` is always within the range [0, 1024].
predicate g_pred() = integer(&g, ?v) &*& 0 <= v &*& v <= 1024;

// Precondition for the thread function.
// Each thread needs a fractional permission to the spinlock to be able to acquire it.
predicate_family_instance pthread_run_pre(threadfn)(void *_unused, any info) =
    [?f]pthread_spinlock(&g_lock, ?lockId, g_pred);

// Postcondition for the thread function.
// Each thread returns its fractional permission, ensuring it's not lost.
predicate_family_instance pthread_run_post(threadfn)(void *_unused, any info) =
    [f]pthread_spinlock(&g_lock, lockId, g_pred);
@*/


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
    //@ : pthread_run_joinable
 {
  pthread_spin_lock(&g_lock);
  //@ open g_pred();

  if (g < 1024) {
    g = g + 1;
  }

  //@ close g_pred();
  pthread_spin_unlock(&g_lock);

  return ((void *) 0);
 }