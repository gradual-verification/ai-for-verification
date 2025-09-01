#include "stdlib.h"
#include "malloc.h"
#include "threading.h"

#define NUM 3

static int counter = 0;

struct shared {
    struct mutex *mtx;
};

//@ predicate counter_invariant() = counter |-> ?c &*& 0 <= c;

//@ predicate shared(struct shared *s) = s->mtx |-> ?mtx &*& mutex(mtx, counter_invariant);

void worker(struct shared *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(worker)(data, ?info);
    //@ ensures thread_run_post(worker)(data, info);
{
    struct shared *s = data;
    //@ open thread_run_pre(worker)(data, info);
    //@ open shared(data);
    mutex_acquire(s->mtx);
    //@ open counter_invariant();
    
    int tmp = counter;
    if (tmp == INT_MAX) {
        abort();
    }
    counter = tmp + 1;
    
    //@ close counter_invariant();
    mutex_release(s->mtx);
    //@ close shared(data);
   //@ close thread_run_post(worker)(data, info);

}

//@ predicate_family_instance thread_run_pre(worker)(struct shared *data, any info) = shared(data);
//@ predicate_family_instance thread_run_post(worker)(struct shared *data, any info) = shared(data);

