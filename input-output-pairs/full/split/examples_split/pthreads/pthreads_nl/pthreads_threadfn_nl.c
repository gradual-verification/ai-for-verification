
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
 {
  pthread_spin_lock(&g_lock);

  if (g < 1024) { g = g + 1; }

  pthread_spin_unlock(&g_lock);

  return ((void *) 0);
 }

