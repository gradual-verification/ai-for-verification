#include "stdlib.h"
#include "malloc.h"
#include "threading.h"

#define NUM 3

static int counter = 0;

struct shared {
    struct mutex *mtx;
};

/*@
predicate_ctor shared_inv()() =
  counter |-> ?v &*& v >= 0;

predicate_family_instance thread_run_pre(worker)(struct shared *s, any info) = 
    [1/NUM] s->mtx |-> ?m &*& [1/NUM] mutex(m, shared_inv) &*& [1/NUM] malloc_block_shared(s);

predicate_family_instance thread_run_post(worker)(struct shared *s, any info) = 
    [1/NUM] s->mtx |-> ?m &*& [1/NUM] mutex(m, shared_inv) &*& [1/NUM] malloc_block_shared(s);
@*/

void worker(struct shared *s) //@ : thread_run_joinable
    //@ requires thread_run_pre(worker)(s, ?info);
    //@ ensures thread_run_post(worker)(s, info);
{
    //@ open thread_run_pre(worker)(s, info);
    mutex_acquire(s->mtx);
    //@ open shared_inv()();
    int tmp = counter;
    if (tmp == INT_MAX) {
        abort();
    }
    counter = tmp + 1;
    //@ close shared_inv()();
    mutex_release(s->mtx);
    //@ close thread_run_post(worker)(s, info);
}