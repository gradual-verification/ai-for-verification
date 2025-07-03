#include "stdlib.h"
#include "malloc.h"
#include "threading.h"

#define NUM 3

static int counter = 0;
//@ static int counter; // VeriFast declaration for global variable

struct shared {
    struct mutex *mtx;
};

/*@
predicate_ctor shared_inv(struct shared *s)() =
  counter |-> ?v &*& v >= 0;    

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
    //@ open thread_run_pre(worker)(s, info);
    mutex_acquire(s->mtx);
    //@ open shared_inv(s)();
    
    int tmp = counter;
    if (tmp == INT_MAX) {
        abort();
    }
    counter = tmp + 1;
    //@ close shared_inv(s)();
    
    mutex_release(s->mtx);
    //@ close thread_run_post(worker)(s, info);
}

void run_workers()
    //@ requires counter |-> 0;
    //@ ensures counter |-> ?v &*& v >= 0;
{
    struct shared *s = malloc(sizeof(struct shared));
    if (s == 0) abort();
    
    //@ close shared_inv(s)();
    //@ close create_mutex_ghost_arg(shared_inv(s));
    s->mtx = create_mutex();
    
    // Split mutex pointer and mutex into NUM fractions
    //@ split_fraction s->mtx |-> s->mtx to [1/NUM]s->mtx |-> s->mtx, [2/NUM]s->mtx |-> s->mtx;
    //@ split_fraction [2/NUM]s->mtx |-> s->mtx to [1/NUM]s->mtx |-> s->mtx, [1/NUM]s->mtx |-> s->mtx;
    //@ split_fraction mutex(s->mtx, shared_inv(s)) to [1/NUM]mutex(s->mtx, shared_inv(s)), [2/NUM]mutex(s->mtx, shared_inv(s));
    //@ split_fraction [2/NUM]mutex(s->mtx, shared_inv(s)) to [1/NUM]mutex(s->mtx, shared_inv(s)), [1/NUM]mutex(s->mtx, shared_inv(s));
    
    for (int i = 0; i < NUM; i++)
    {
        //@ close thread_run_pre(worker)(s, unit);
        struct thread *t = thread_start_joinable(worker, s);
        thread_join(t);
        //@ open thread_run_post(worker)(s, unit);
    }
    
    // Merge fractions back
    //@ merge_fractions s->mtx |-> s->mtx;
    //@ merge_fractions mutex(s->mtx, shared_inv(s));
    
    mutex_dispose(s->mtx);
    //@ open shared_inv(s)();
    free(s);
}