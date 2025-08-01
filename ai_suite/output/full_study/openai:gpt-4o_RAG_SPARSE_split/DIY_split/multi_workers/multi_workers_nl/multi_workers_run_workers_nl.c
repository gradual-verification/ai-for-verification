#include "stdlib.h"
#include "malloc.h"
#include "threading.h"

#define NUM 3

static int counter = 0;

struct shared {
    struct mutex *mtx;
};

/*@
predicate_ctor shared_inv(struct shared *s)() =
    [1/2]integer(&counter, ?c) &*& c >= 0;

predicate_family_instance thread_run_pre(worker)(struct shared *data, any info) =
    [1/2]data->mtx |-> ?mtx &*& [1/3]mutex(mtx, shared_inv(data));

predicate_family_instance thread_run_post(worker)(struct shared *data, any info) =
    [1/2]data->mtx |-> ?mtx &*& [1/3]mutex(mtx, shared_inv(data));
@*/

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
    struct shared *s = data;
    //@ open thread_run_pre(worker)(data, info);
    mutex_acquire(s->mtx);
    //@ open shared_inv(s)();
    
    int tmp = counter;
    if (tmp == INT_MAX) {
        abort();
    }
    counter = tmp + 1;
    
    //@ close shared_inv(s)();
    mutex_release(s->mtx);
    //@ close thread_run_post(worker)(data, info);
}

// TODO: make this function pass the verification
/***
 * Description:
 * The `run_workers` function creates a shared data structure, starts multiple worker threads, and waits for them to finish.
 *
 * It requires that counter is initialized to 0 and ensures that the counter is non-negative after all workers have finished.
 */
/*@
predicate_family_instance thread_run_pre(run_workers)() =
    integer(&counter, 0);

predicate_family_instance thread_run_post(run_workers)() =
    integer(&counter, ?c) &*& c >= 0;
@*/
void run_workers() //@ : thread_run
    //@ requires thread_run_pre(run_workers)();
    //@ ensures thread_run_post(run_workers)();
{
    struct shared *s = malloc(sizeof(struct shared));
    if (s == 0) abort();
    //@ close shared_inv(s)();
    //@ close create_mutex_ghost_arg(shared_inv(s));
    s->mtx = create_mutex();
    
    for (int i = 0; i < NUM; i++)
    {
        //@ close thread_run_pre(worker)(s, unit);
        struct thread *t = thread_start_joinable(worker, s);
        thread_join(t);
        //@ open thread_run_post(worker)(s, unit);
    }
    
    mutex_dispose(s->mtx);
    //@ open shared_inv(s)();
    free(s);
}