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
    [1/NUM]s->mtx |-> ?m &*& [1/NUM]mutex(m, shared_inv(s));

predicate_family_instance thread_run_post(worker)(struct shared *s, any info) = 
    [1/NUM]s->mtx |-> ?m &*& [1/NUM]mutex(m, shared_inv(s));
@*/

void worker(struct shared *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(worker)(data, ?info);
    //@ ensures thread_run_post(worker)(data, info);
{
    struct shared *s = data;
    //@ open thread_run_pre(worker)(data, info);
    mutex_acquire(s->mtx);
    //@ open shared_inv(s)();
    
    int tmp = counter;
    if (tmp == INT_MAX) {
        abort();
    }
    counter = tmp + 1;
    
    //@ close shared_inv(s)();
    mutex_release(s->mtx);
    //@ close thread_run_post(worker)(data, info);
}

// Helper function to create and initialize shared structure
struct shared *create_shared()
    //@ requires true;
    //@ ensures result != 0 &*& shared_inv(result)() &*& malloc_block_shared(result);
{
    struct shared *s = malloc(sizeof(struct shared));
    if (s == 0) abort();
    
    //@ close shared_inv(s)();
    //@ close create_mutex_ghost_arg(shared_inv(s));
    s->mtx = create_mutex();
    //@ close malloc_block_shared(s);
    return s;
}

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct shared *s = create_shared();
    
    // Start worker threads
    //@ close thread_run_pre(worker)(s, unit);
    struct thread *t1 = thread_start_joinable(worker, s);
    //@ close thread_run_pre(worker)(s, unit);
    struct thread *t2 = thread_start_joinable(worker, s);
    //@ close thread_run_pre(worker)(s, unit);
    struct thread *t3 = thread_start_joinable(worker, s);
    
    // Join worker threads
    thread_join(t1);
    //@ open thread_run_post(worker)(s, unit);
    thread_join(t2);
    //@ open thread_run_post(worker)(s, unit);
    thread_join(t3);
    //@ open thread_run_post(worker)(s, unit);
    
    // Cleanup
    mutex_dispose(s->mtx);
    //@ open shared_inv(s)();
    free(s);
    
    return 0;
}