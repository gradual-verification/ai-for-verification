#include "stdlib.h"
#include "malloc.h"
#include "threading.h"

#define NUM 3

static int counter = 0;

//@ predicate_ctor counter_inv()() = counter |-> ?c &*& c >= 0;

struct shared {
    struct mutex *mtx;
};

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
//@ requires thread_run_data(worker)(data);
//@ ensures true;
{
    //@ open thread_run_data(worker)(data);
    struct shared *s = data;
    mutex_acquire(s->mtx);
    //@ open counter_inv()();
    
    int tmp = counter;
    //@ assert tmp >= 0;
    if (tmp == INT_MAX) {
        abort();
    }
    counter = tmp + 1;
    //@ assert counter >= 0;
    //@ close counter_inv()();

    mutex_release(s->mtx);
}

/*@
predicate_family_instance thread_run_data(worker)(struct shared *data) =
    data != 0 &*& data->mtx |-> ?mtx &*& [_]mutex(mtx, counter_inv);
@*/