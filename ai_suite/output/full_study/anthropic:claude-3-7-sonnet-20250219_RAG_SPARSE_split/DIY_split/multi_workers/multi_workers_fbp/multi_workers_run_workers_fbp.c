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
    //@ open thread_run_pre(worker)(data, info);
    //@ close thread_run_post(worker)(data, info);
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
    
    // @ assert mutex(s->mtx, shared_inv(s));
    //@ assert s->mtx |-> ?m;
    
    // @ produce_fraction_fraction(s->mtx |-> m);
    // @ produce_fraction_fraction(s->mtx |-> m);
    // @ produce_fraction_fraction(s->mtx |-> m);
    
    //@ assert [1/3]s->mtx |-> m &*& [1/3]s->mtx |-> m &*& [1/3]s->mtx |-> m;
    // @ produce_fraction_fraction(mutex(m, shared_inv(s)));
    // @ produce_fraction_fraction(mutex(m, shared_inv(s)));
    // @ produce_fraction_fraction(mutex(m, shared_inv(s)));
    
    for (int i = 0; i < NUM; i++)
        /*@ invariant s->mtx |-> ?mtx &*& 
        i >= 0 &*& i <= NUM &*& 
        mutex(mtx, shared_inv(s)); @*/
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