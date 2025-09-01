#include "stdlib.h"
#include "malloc.h"
#include "threading.h"

#define NUM 3

static int counter = 0;


struct shared {
    struct mutex *mtx;
};

/*@
// Predicate for the shared counter. It serves as the invariant for the mutex.
// It asserts that 'counter' holds a valid integer value 'v' and that 'v' is non-negative.
predicate counter_inv() = counter |-> ?v &*& 0 <= v;

// Predicate describing the memory layout of the 'shared' struct.
// It holds a pointer to the mutex and the memory block for the struct itself.
predicate shared_struct(struct shared *s; struct mutex *mtx) =
    s->mtx |-> mtx &*&
    malloc_block_shared(s);

// Precondition for the 'worker' thread.
// It requires the shared struct and a fractional permission for the mutex.
// The fraction allows multiple threads to share the mutex.
predicate_family_instance thread_run_pre(worker)(void *data, any info) =
    shared_struct((struct shared *)data, ?mtx) &*&
    [?f]mutex(mtx, counter_inv);

// Postcondition for the 'worker' thread.
// It ensures that the resources taken by the thread are returned upon completion.
predicate_family_instance thread_run_post(worker)(void *data, any info) =
    shared_struct((struct shared *)data, ?mtx) &*&
    [?f]mutex(mtx, counter_inv);
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `worker` function acquires exclusive access and increments the counter.
 *
 * @param data: the shared data structure containing the mutex
 * 
 * It requires and ensures that that the counter is non-negative.
 */
void worker(struct shared *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(worker)(data, ?info) &*& lockset(currentThread, nil);
    //@ ensures thread_run_post(worker)(data, info) &*& lockset(currentThread, nil);
{
    //@ open thread_run_pre(worker)(data, info);
    struct shared *s = data;
    //@ open shared_struct(s, ?mtx);
    mutex_acquire(s->mtx);
    //@ open counter_inv();
    
    int tmp = counter;
    if (tmp == INT_MAX) {
        abort();
    }
    counter = tmp + 1;

    //@ close counter_inv();
    mutex_release(s->mtx);
    
    //@ close shared_struct(s, mtx);
    //@ close thread_run_post(worker)(data, info);
}