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

// TODO: make this function pass the verification
void run_workers()
    //@ requires counter |-> 0;
    //@ ensures counter |-> ?v &*& v >= 0;
{
    struct shared *s = malloc(sizeof(struct shared));
    if (s == 0) abort();
    s->mtx = create_mutex();
    //@ close shared_inv(s)();
    //@ close create_mutex_ghost_arg(shared_inv(s));
    //@ close [1/NUM]s->mtx |-> s->mtx;
    //@ close [1/NUM]mutex(s->mtx, shared_inv(s));

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