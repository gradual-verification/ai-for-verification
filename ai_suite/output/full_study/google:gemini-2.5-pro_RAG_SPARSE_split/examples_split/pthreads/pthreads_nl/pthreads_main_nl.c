#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>

/*@
// The invariant for the spinlock. It protects the global variable 'g'
// and ensures its value is within the specified range.
predicate g_inv() = integer(&g, ?v) &*& 0 <= v &*& v <= 1024;

// Predicate families for the thread's run function.
// 'threadfn' does not use its arguments, so the pre/post conditions are simple.
predicate_family_instance pthread_run_pre(threadfn)(void *data, any info) =
    data == (void*)0 &*& info == nil;
predicate_family_instance pthread_run_post(threadfn)(void *data, any info) =
    data == (void*)0 &*& info == nil;
@*/

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
void *threadfn(void* _unused) //@ : pthread_run_joinable
    //@ requires pthread_run_pre(threadfn)(_unused, ?info);
    //@ ensures pthread_run_post(threadfn)(_unused, info) &*& result == 0;
{
    //@ open pthread_run_pre(threadfn)(_unused, info);
    pthread_spin_lock(&g_lock);
    //@ open g_inv();

    if (g < 1024) {
        g = g + 1;
    }

    //@ close g_inv();
    pthread_spin_unlock(&g_lock);
    //@ close pthread_run_post(threadfn)(_unused, info);

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
/*@
// Precondition for run_instance: requires ownership of the global variables.
predicate run_instance_pre() = integer(&g, _) &*& integer(&g_lock, _);
// Postcondition for run_instance: this function never returns because it calls exit(0).
predicate run_instance_post() = false;
@*/
void run_instance(void) //@ : pre_post(run_instance_pre, run_instance_post)
{
    //@ open run_instance_pre();
    void *data = (void *) 0;
    pthread_t pthr1, pthr2;

    g = 41;
    //@ close g_inv();
    //@ close create_spinlock_ghost_args(g_inv, nil, nil);
    pthread_spin_init(&g_lock, 0);

    //@ close pthread_run_pre(threadfn)(data, nil);
    pthread_create(&pthr2, (void *) 0, &threadfn, data);
    //@ close pthread_run_pre(threadfn)(data, nil);
    pthread_create(&pthr1, (void *) 0, &threadfn, data);

    sleep(600);
    pthread_spin_lock(&g_lock);
    //@ open g_inv();
    g = 55;
    //@ close g_inv();
    pthread_spin_unlock(&g_lock);
    sleep(600);

    pthread_join(pthr2, (void *) 0);
    //@ open pthread_run_post(threadfn)(data, nil);

    pthread_join(pthr1, (void *) 0);
    //@ open pthread_run_post(threadfn)(data, nil);

    pthread_spin_destroy(&g_lock);
    //@ open g_inv();
    //@ leak integer(&g, _);

    exit(0);
    //@ assert false; // This line is unreachable.
}


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
/*@
// Custom specification for the main function.
// It requires ownership of the global variables and command-line arguments.
// It ensures 'false' because run_instance calls exit(0) and never returns.
typedef int custom_main_spec(int argc, char** argv);
    requires integer(&g, _) &*& integer(&g_lock, _) &*&
             0 <= argc &*& [_]argv(argv, argc, ?arguments);
    ensures false;
@*/
int main (int argc, char** argv) //@ : custom_main_spec
{
    //@ close run_instance_pre();
    run_instance();

    return (0); // This line is unreachable.
}