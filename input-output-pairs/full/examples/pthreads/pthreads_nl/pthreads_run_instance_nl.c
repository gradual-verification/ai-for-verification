
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
 * Function: run_instance
 *
 * Description:
 * Initializes shared state and synchronization primitives, spawns two threads to run `threadfn`,
 * updates the global variable `g` in the main thread under lock protection, and then joins all threads.
 *
 * Demonstrates:
 * - Spinlock initialization and use
 * - Safe multi-threaded access to shared data
 * - Thread creation and synchronization with `pthread_create` and `pthread_join`
 *
 * It requires that g is within the range [0, 1024].
 */
void run_instance(void)
 {
  void *data = (void *) 0;
  pthread_t pthr1, pthr2;

  g = 41;

  pthread_spin_init(&g_lock, 0);

  pthread_create(&pthr2, (void *) 0, &threadfn, data);
  pthread_create(&pthr1, (void *) 0, &threadfn, data);

  sleep(600);
  pthread_spin_lock(&g_lock);
  g = 55;
  pthread_spin_unlock(&g_lock);
  sleep(600);

  pthread_join(pthr2, (void *) 0);

  pthread_join(pthr1, (void *) 0);

  pthread_spin_destroy(&g_lock);

  exit(0);
 }

