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
    
    //@ close shared_inv(s)();
    //@ close create_mutex_ghost_arg(shared_inv(s));
    s->mtx = create_mutex();
    
    //@ assert s->mtx |-> ?m;
    //@ assert mutex(m, shared_inv(s));
    
    //@ split_fraction s->mtx |-> _, 1/NUM;
    //@ split_fraction mutex(m, shared_inv(s)), 1/NUM;
    
    for (int i = 0; i < NUM; i++)
    //@ invariant counter |-> ?cv &*& cv >= 0 &*& malloc_block_shared(s) &*& s->mtx |-> ?mtx &*& 
    //@ (NUM - i) * [1/NUM]s->mtx |-> mtx &*& (NUM - i) * [1/NUM]mutex(mtx, shared_inv(s));
    {
        //@ close thread_run_pre(worker)(s, unit);
        struct thread *t = thread_start_joinable(worker, s);
        thread_join(t);
        //@ open thread_run_post(worker)(s, unit);
    }
    
    //@ merge_fractions s->mtx |-> _;
    //@ merge_fractions mutex(_, _);
    
    mutex_dispose(s->mtx);
    //@ open shared_inv(s)();
    free(s);
}