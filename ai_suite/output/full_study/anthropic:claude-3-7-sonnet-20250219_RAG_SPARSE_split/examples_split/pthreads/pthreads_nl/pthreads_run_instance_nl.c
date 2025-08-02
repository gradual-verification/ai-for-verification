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
// Define a predicate for the lock invariant
predicate g_lock_invariant() = integer(&g, ?value) &*& 0 <= value &*& value <= 1024;

// Define a predicate for the thread function's pre/post conditions
predicate_family_instance pthread_run_pre(threadfn)(void* _unused, any info) = 
    [_]g_lock_invariant() &*& emp;

predicate_family_instance pthread_run_post(threadfn)(void* _unused, any info) = 
    emp;
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
//@ requires pthread_run_pre(threadfn)(_unused, ?info);
//@ ensures pthread_run_post(threadfn)(_unused, info);
{
  //@ open pthread_run_pre(threadfn)(_unused, info);
  pthread_spin_lock(&g_lock);
  //@ open g_lock_invariant();

  if (g < 1024) { g = g + 1; }
  //@ assert 0 <= g &*& g <= 1024;
  
  //@ close g_lock_invariant();
  pthread_spin_unlock(&g_lock);

  //@ close pthread_run_post(threadfn)(_unused, info);
  return ((void *) 0);
}


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
//@ requires true;
//@ ensures true;
{
  void *data = (void *) 0;
  pthread_t pthr1, pthr2;

  g = 41;
  //@ assert 0 <= g &*& g <= 1024;
  
  //@ close create_lock_ghost_args(g_lock_invariant, nil, nil);
  //@ close g_lock_invariant();
  pthread_spin_init(&g_lock, 0);

  //@ close pthread_run_pre(threadfn)(data, unit);
  pthread_create(&pthr2, (void *) 0, &threadfn, data);
  //@ close pthread_run_pre(threadfn)(data, unit);
  pthread_create(&pthr1, (void *) 0, &threadfn, data);

  sleep(600);
  pthread_spin_lock(&g_lock);
  //@ open g_lock_invariant();
  g = 55;
  //@ assert 0 <= g &*& g <= 1024;
  //@ close g_lock_invariant();
  pthread_spin_unlock(&g_lock);
  sleep(600);

  pthread_join(pthr2, (void *) 0);
  //@ open pthread_run_post(threadfn)(_, _);

  pthread_join(pthr1, (void *) 0);
  //@ open pthread_run_post(threadfn)(_, _);

  pthread_spin_destroy(&g_lock);
  //@ open g_lock_invariant();

  exit(0);
}