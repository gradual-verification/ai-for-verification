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
  s->mtx |-> ?m &*& [1/NUM]mutex(m, shared_inv(s)) &*& counter |-> ?v &*& v >= 0 &*& malloc_block_shared(s);    

predicate_family_instance thread_run_pre(worker)(struct shared *s, any info) = 
    [1/NUM] s->mtx |-> ?m &*& [1/NUM] mutex(m, shared_inv(s));

predicate_family_instance thread_run_post(worker)(struct shared *s, any info) = 
    [1/NUM] s->mtx |-> ?m &*& [1/NUM] mutex(m, shared_inv(s));
@*/

// TODO: make this function pass the verification
void worker(struct shared *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(worker)(data, ?info);
    //@ ensures thread_run_post(worker)(data, info);
{
    struct shared *s = data;
    mutex_acquire(s->mtx);
    //@ open shared_inv(s)();
    
    int tmp = counter;
    if (tmp == INT_MAX) {
        abort();
    }
    counter = tmp + 1;
    
    //@ close shared_inv(s)();
    mutex_release(s->mtx);
}