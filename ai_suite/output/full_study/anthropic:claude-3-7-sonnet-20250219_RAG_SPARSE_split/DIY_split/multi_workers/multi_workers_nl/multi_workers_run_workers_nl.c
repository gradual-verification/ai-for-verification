#include "stdlib.h"
#include "malloc.h"
#include "threading.h"

#define NUM 3

static int counter = 0;

//@ predicate counter_inv() = integer(&counter, ?c) &*& c >= 0;

struct shared {
    struct mutex *mtx;
};

//@ predicate shared(struct shared *s) = s->mtx |-> ?mtx &*& mutex(mtx, counter_inv) &*& malloc_block_shared(s);

/***
 * Description:
 * The `worker` function acquires exclusive access and increments the counter.
 *
 * @param data: the shared data structure containing the mutex
 * 
 * It requires and ensures that that the counter is non-negative.
 */
/*@
predicate_family_instance thread_run_joinable_pre(worker)(struct shared *data, unit u) = 
    [1/NUM]shared(data);

predicate_family_instance thread_run_joinable_post(worker)(struct shared *data, unit u) = 
    [1/NUM]shared(data);
@*/

void worker(struct shared *data) //@ : thread_run_joinable
//@ requires thread_run_joinable_pre(worker)(data, unit) &*& lockset(currentThread, nil);
//@ ensures thread_run_joinable_post(worker)(data, unit) &*& lockset(currentThread, nil);
{
    //@ open thread_run_joinable_pre(worker)(data, _);
    struct shared *s = data;
    //@ open [1/NUM]shared(s);
    mutex_acquire(s->mtx);
    //@ open counter_inv();
    
    int tmp = counter;
    if (tmp == INT_MAX) {
        abort();
    }
    counter = tmp + 1;
    //@ close counter_inv();

    mutex_release(s->mtx);
    //@ close [1/NUM]shared(s);
    //@ close thread_run_joinable_post(worker)(data, unit);
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
//@ ensures integer(&counter, ?c) &*& c >= 0;
{
    //@ close counter_inv();
    struct shared *s = malloc(sizeof(struct shared));
    if (s == 0) abort();
    
    //@ close create_mutex_ghost_arg(counter_inv);
    s->mtx = create_mutex();
    
    //@ close shared(s);
    
    struct thread *threads[NUM];
    
    for (int i = 0; i < NUM; i++)
        //@ invariant integer_strict(i, i) &*& 0 <= i &*& i <= NUM &*& [1-i*1/NUM]shared(s) &*& is_thread_array(threads, i);
    {
        //@ assert [1-i*1/NUM]shared(s);
        //@ produce_fraction shared(s);
        //@ close thread_run_joinable_pre(worker)(s, unit);
        threads[i] = thread_start_joinable(worker, s);
    }
    
    for (int i = 0; i < NUM; i++)
        //@ invariant integer_strict(i, i) &*& 0 <= i &*& i <= NUM &*& [i*1/NUM]shared(s) &*& is_thread_array(threads, NUM) &*& is_joined_array(threads, i);
    {
        thread_join(threads[i]);
        //@ open thread_run_joinable_post(worker)(s, _);
        //@ consume_fraction shared(s);
    }
    
    //@ open shared(s);
    mutex_dispose(s->mtx);
    free(s);
    //@ open counter_inv();
}