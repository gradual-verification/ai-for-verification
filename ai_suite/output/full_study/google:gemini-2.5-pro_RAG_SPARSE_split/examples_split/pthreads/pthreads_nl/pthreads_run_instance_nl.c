#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>

/*@
// Predicate for the shared global variable 'g' and its invariant.
predicate g_pred(int val) =
    g |-> val &*& 0 <= val &*& val <= 1024;

// Lock invariant for g_lock. This predicate is protected by the spinlock.
predicate_ctor g_inv()() = g_pred(_);

// A ghost data structure to pass the lockId to the thread's specification.
inductive thread_info = thread_info_ctor(int lockId);

// Pre- and post-conditions for the thread function.
// Each thread needs a fraction of the spinlock predicate to be able to acquire it.
// We split the lock permission into 3 parts: one for each of the two
// created threads, and one for the main thread.
predicate_family_instance pthread_run_pre(threadfn)(void *_unused, any info) =
    switch (info) {
        case thread_info_ctor(lockId):
            return [1/3]pthread_spinlock(&g_lock, lockId, g_inv);
        case _:
            return false;
    };

predicate_family_instance pthread_run_post(threadfn)(void *_unused, any info) =
    switch (info) {
        case thread_info_ctor(lockId):
            return [1/3]pthread_spinlock(&g_lock, lockId, g_inv);
        case _:
            return false;
    };
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
void *threadfn(void* _unused)
    //@ : pthread_run_joinable
    //@ requires pthread_run_pre(threadfn)(_unused, ?info);
    //@ ensures pthread_run_post(threadfn)(_unused, info) &*& result == 0;
{
    //@ open pthread_run_pre(threadfn)(_unused, info);
    //@ switch(info) { case thread_info_ctor(lockId): default: }

    pthread_spin_lock(&g_lock);
    //@ open g_inv()();
    //@ open g_pred(?val);

    if (g < 1024) {
        g = g + 1;
    }

    //@ int new_val = (val < 1024) ? val + 1 : val;
    //@ assert g |-> new_val;
    //@ assert 0 <= new_val &*& new_val <= 1024;
    //@ close g_pred(new_val);
    //@ close g_inv()();
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
/*@
predicate run_instance_pre() =
    g |-> _ &*& g_lock |-> _;
@*/
void run_instance(void)
    //@ requires run_instance_pre();
    //@ ensures false;
{
    //@ open run_instance_pre();
    void *data = (void *) 0;
    pthread_t pthr1, pthr2;

    g = 41;

    //@ close g_pred(41);
    //@ close g_inv()();
    //@ close create_spinlock_ghost_args(g_inv, nil, nil);
    pthread_spin_init(&g_lock, 0);
    //@ assert [1.0]pthread_spinlock(&g_lock, ?lockId, g_inv);

    //@ close pthread_run_pre(threadfn)(data, thread_info_ctor(lockId));
    pthread_create(&pthr2, (void *) 0, &threadfn, data);
    //@ close pthread_run_pre(threadfn)(data, thread_info_ctor(lockId));
    pthread_create(&pthr1, (void *) 0, &threadfn, data);

    sleep(600);
    pthread_spin_lock(&g_lock);
    //@ open g_inv()();
    //@ open g_pred(_);
    g = 55;
    //@ close g_pred(55);
    //@ close g_inv()();
    pthread_spin_unlock(&g_lock);
    sleep(600);

    pthread_join(pthr2, (void *) 0);
    //@ open pthread_run_post(threadfn)(data, thread_info_ctor(lockId));

    pthread_join(pthr1, (void *) 0);
    //@ open pthread_run_post(threadfn)(data, thread_info_ctor(lockId));

    pthread_spin_destroy(&g_lock);
    //@ open g_inv()();
    //@ open g_pred(final_g);
    //@ leak g |-> final_g;

    exit(0);
}