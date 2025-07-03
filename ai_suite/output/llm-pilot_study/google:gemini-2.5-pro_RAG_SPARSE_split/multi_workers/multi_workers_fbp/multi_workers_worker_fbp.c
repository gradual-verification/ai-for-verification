#include "stdlib.h"
#include "malloc.h"
#include "threading.h"

#define NUM 3

static int counter = 0;


struct shared {
    struct mutex *mtx;
};

/*@
// A precise predicate describing the shared struct's memory layout.
// This allows sharing read-only access to the struct.
// 'm' is an output parameter; its value is determined by 's'.
predicate shared_struct(struct shared *s; struct mutex *m) =
    s->mtx |-> m &*& malloc_block_shared(s);

// The invariant for the mutex. It protects the global counter.
// It is parameterized by 's' to associate it with a specific shared resource instance.
predicate_ctor shared_inv(struct shared *s)() =
  counter |-> ?v &*& v >= 0;

// The pre- and post-conditions for the worker thread.
// Each thread gets a fraction of the shared struct predicate and the mutex predicate.
predicate_family_instance thread_run_pre(worker)(struct shared *s, any info) =
    [1/NUM]shared_struct(s, ?m) &*& [1/NUM]mutex(m, shared_inv(s));

predicate_family_instance thread_run_post(worker)(struct shared *s, any info) =
    [1/NUM]shared_struct(s, ?m) &*& [1/NUM]mutex(m, shared_inv(s));
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