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
  counter |-> ?v &*& v >= 0 &*& malloc_block_shared(s);    

predicate_family_instance thread_run_pre(worker)(struct shared *s, any info) = 
    [1/NUM] s->mtx |-> ?m &*& [1/NUM] mutex(m, shared_inv(s));

predicate_family_instance thread_run_post(worker)(struct shared *s, any info) = 
    [1/NUM] s->mtx |-> ?m &*& [1/NUM] mutex(m, shared_inv(s));
@*/

void worker(struct shared *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(worker)(data, ?info);
    //@ ensures thread_run_post(worker)(data, info);
{
    struct shared *s = data;
    mutex_acquire(s->mtx);
    
    int tmp = counter;
    if (tmp == INT_MAX) {
        abort();
    }
    counter = tmp + 1;

    mutex_release(s->mtx);
}

void run_workers()
    //@ requires counter |-> 0;
    //@ ensures counter |-> ?v &*& v >= 0;
{
    //@ open counter |-> 0;
    struct shared *s = malloc(sizeof(struct shared));
    if (s == 0) abort();
    
    //@ close shared_inv(s)();
    //@ close create_mutex_ghost_arg(shared_inv(s));
    s->mtx = create_mutex();
    
    //@ close thread_run_pre(worker)(s, unit);
    struct thread *t1 = thread_start_joinable(worker, s);
    //@ close thread_run_pre(worker)(s, unit);
    struct thread *t2 = thread_start_joinable(worker, s);
    //@ close thread_run_pre(worker)(s, unit);
    struct thread *t3 = thread_start_joinable(worker, s);
    
    thread_join(t1);
    //@ open thread_run_post(worker)(s, unit);
    thread_join(t2);
    //@ open thread_run_post(worker)(s, unit);
    thread_join(t3);
    //@ open thread_run_post(worker)(s, unit);
    
    //@ open shared_inv(s)();
    mutex_dispose(s->mtx);
    free(s);
    //@ close counter |-> _;
}