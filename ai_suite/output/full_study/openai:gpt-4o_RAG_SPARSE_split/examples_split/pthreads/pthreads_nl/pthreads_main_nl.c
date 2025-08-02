#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>

/***
 * Variable: g
 * Description:
 * A global integer shared between threads, protected by a spinlock.
 */
//@ predicate g_pred() = integer(&g, ?v) &*& 0 <= v &*& v <= 1024;
static int g;

/***
 * Variable: g_lock
 * Description:
 * A spinlock used to synchronize access to the shared global variable `g`.
 */
//@ predicate g_lock_pred() = g_pred();
pthread_spinlock_t g_lock;

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
//@ predicate_family_instance pthread_run_pre(threadfn)(void *data, any info) = g_pred();
//@ predicate_family_instance pthread_run_post(threadfn)(void *data, any info) = g_pred();
void *threadfn(void* _unused)
    //@ requires pthread_run_pre(threadfn)(_unused, ?info);
    //@ ensures pthread_run_post(threadfn)(_unused, info);
{
    pthread_spin_lock(&g_lock);
    //@ open g_pred();
    if (g < 1024) { g = g + 1; }
    //@ close g_pred();
    pthread_spin_unlock(&g_lock);
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
//@ predicate run_instance_pred() = g_pred() &*& pthread_spinlock(&g_lock, ?lockId, g_lock_pred);
void run_instance(void)
    //@ requires run_instance_pred();
    //@ ensures run_instance_pred();
{
    void *data = (void *) 0;
    pthread_t pthr1, pthr2;

    g = 41;
    //@ close g_pred();
    pthread_spin_init(&g_lock, 0);
    //@ close pthread_spinlock(&g_lock, ?lockId, g_lock_pred);

    pthread_create(&pthr2, (void *) 0, &threadfn, data);
    pthread_create(&pthr1, (void *) 0, &threadfn, data);

    sleep(600);
    pthread_spin_lock(&g_lock);
    //@ open g_pred();
    g = 55;
    //@ close g_pred();
    pthread_spin_unlock(&g_lock);
    sleep(600);

    pthread_join(pthr2, (void *) 0);
    pthread_join(pthr1, (void *) 0);

    pthread_spin_destroy(&g_lock);
    //@ open pthread_spinlock(&g_lock, lockId, g_lock_pred);

    exit(0);
}

// TODO: make this function pass the verification
/***
 * Function: main
 *
 * Description:
 * Calls `run_instance` to start the multi-threaded execution and manage shared state updates.
 *
 * @param argc - number of command-line arguments (unused).
 * @param argv - array of command-line arguments (unused).
 * @return 0 on successful termination.
 */
//@ predicate_family_instance custom_main_spec(main)(int argc, char **argv) = module(main, true);
int main (int argc, char** argv)
    //@ requires custom_main_spec(main)(argc, argv);
    //@ ensures true;
{
    //@ close run_instance_pred();
    run_instance();
    return (0);
}