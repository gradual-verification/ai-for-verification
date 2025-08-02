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
// Define a predicate to represent the protected resource
predicate g_resource() = integer(&g, ?value) &*& 0 <= value &*& value <= 1024;

// Define a predicate for the lock
predicate g_lock_pred(pthread_spinlock_t *lock) = 
    pthread_spinlock(lock, ?lockId, g_resource);

// Define a predicate for the locked state
predicate g_lock_held(pthread_spinlock_t *lock, int threadId, real frac) = 
    pthread_spinlock_locked(lock, ?lockId, g_resource, threadId, frac);

// Define a predicate for thread function
predicate_family_instance pthread_run_pre(threadfn)(void *data, any info) =
    [1/2]g_lock_pred(&g_lock);

predicate_family_instance pthread_run_post(threadfn)(void *data, any info) =
    [1/2]g_lock_pred(&g_lock);

// Define a custom main spec
predicate_family_instance custom_main_spec(main)(int argc, char **argv) =
    true;
@*/

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
/*@ requires pthread_run_pre(threadfn)(_unused, ?info); @*/
/*@ ensures pthread_run_post(threadfn)(_unused, info) &*& result == 0; @*/
{
  /*@ open pthread_run_pre(threadfn)(_unused, info); @*/
  
  pthread_spin_lock(&g_lock);
  /*@ open g_resource(); @*/

  if (g < 1024) { g = g + 1; }
  
  /*@ close g_resource(); @*/
  pthread_spin_unlock(&g_lock);
  
  /*@ close pthread_run_post(threadfn)(_unused, info); @*/
  return ((void *) 0);
}


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
/*@ requires true; @*/
/*@ ensures true; @*/
{
  void *data = (void *) 0;
  pthread_t pthr1, pthr2;

  g = 41;
  /*@ close g_resource(); @*/
  
  /*@ close create_lock_ghost_args(g_resource, nil, nil); @*/
  pthread_spin_init(&g_lock, 0);

  /*@ close pthread_run_pre(threadfn)(data, unit); @*/
  pthread_create(&pthr2, (void *) 0, &threadfn, data);
  
  /*@ close pthread_run_pre(threadfn)(data, unit); @*/
  pthread_create(&pthr1, (void *) 0, &threadfn, data);

  sleep(600);
  pthread_spin_lock(&g_lock);
  /*@ open g_resource(); @*/
  g = 55;
  /*@ close g_resource(); @*/
  pthread_spin_unlock(&g_lock);
  sleep(600);

  pthread_join(pthr2, (void *) 0);
  /*@ open pthread_run_post(threadfn)(data, unit); @*/

  pthread_join(pthr1, (void *) 0);
  /*@ open pthread_run_post(threadfn)(data, unit); @*/

  pthread_spin_destroy(&g_lock);
  /*@ open g_resource(); @*/

  exit(0);
}


// TODO: make this function pass the verification
/***
 * Function: main
 *
 * Description:
 * Calls `run_instance` to start the multi-threaded execution and manage shared state updates.
 *
@param argc - number of command-line arguments (unused).
@param argv - array of command-line arguments (unused).
@return 0 on successful termination.
 */
int main (int argc, char** argv) //@ : custom_main_spec
/*@ requires custom_main_spec(main)(argc, argv); @*/
/*@ ensures true; @*/
{
  /*@ open custom_main_spec(main)(argc, argv); @*/
  run_instance();

  return (0);
}