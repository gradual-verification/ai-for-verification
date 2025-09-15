    /*@
    predicate counter_inv() = integer(&counter, ?v) &*& 0 <= v;
    @*/
    /*@
    predicate_family_instance thread_run_pre(worker)(void *data, any info) =
        ((struct shared *)data)->mtx |-> ?mtx &*&
        malloc_block_shared(data) &*&
        mutex(mtx, counter_inv);

    predicate_family_instance thread_run_post(worker)(void *data, any info) =
        ((struct shared *)data)->mtx |-> ?mtx &*&
        malloc_block_shared(data) &*&
        mutex(mtx, counter_inv);
    @*/
#include "stdlib.h"
#include "malloc.h"
#include "threading.h"

#define NUM 3

static int counter = 0;

/*@
predicate counter_inv() = integer(&counter, ?v) &*& 0 <= v;
@*/

struct shared {
    struct mutex *mtx;
};

/*@
predicate_family_instance thread_run_pre(worker)(void *data, any info) =
    ((struct shared *)data)->mtx |-> ?mtx &*&
    malloc_block_shared(data) &*&
    mutex(mtx, counter_inv);

predicate_family_instance thread_run_post(worker)(void *data, any info) =
    ((struct shared *)data)->mtx |-> ?mtx &*&
    malloc_block_shared(data) &*&
    mutex(mtx, counter_inv);
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
    //@ open thread_run_pre(worker)(data, info);
    struct shared *s = data;
    mutex_acquire(s->mtx);
    //@ open counter_inv();
    
    int tmp = counter;
    if (tmp == INT_MAX) {
        abort();
    }
    counter = tmp + 1;
    //@ assert 0 <= tmp + 1;
    //@ close counter_inv();

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
void run_workers()
    //@ requires integer(&counter, 0);
    //@ ensures integer(&counter, ?c) &*& 0 <= c;
{
    //@ open integer(&counter, 0);
    struct shared *s = malloc(sizeof(struct shared));
    if (s == 0) abort();
    
    //@ close counter_inv();
    //@ close create_mutex_ghost_arg(counter_inv);
    s->mtx = create_mutex();
    struct mutex *mtx = s->mtx;
    
    for (int i = 0; i < NUM; i++)
        //@ invariant 0 <= i &*& i <= NUM &*& malloc_block_shared(s) &*& s->mtx |-> mtx &*& mutex(mtx, counter_inv);
    {
        //@ close thread_run_pre(worker)(s, unit);
        struct thread *t = thread_start_joinable(worker, s);
        thread_join(t);
        //@ open thread_run_post(worker)(s, unit);
    }
    
    mutex_dispose(s->mtx);
    
    free(s);
    
    //@ open counter_inv();
}