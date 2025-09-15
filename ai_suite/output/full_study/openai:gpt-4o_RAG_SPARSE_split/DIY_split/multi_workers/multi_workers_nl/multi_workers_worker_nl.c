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
    //@ requires thread_run_pre(worker)(data, ?info) &*& shared(data);
    //@ ensures thread_run_post(worker)(data, info) &*& shared(data);
{
    struct shared *s = data;
    mutex_acquire(s->mtx);
    //@ open counter_invariant();
    
    int tmp = counter;
    if (tmp == INT_MAX) {
        abort();
    }
    counter = tmp + 1;
    
    //@ close counter_invariant();
    mutex_release(s->mtx);
}

//@ predicate_family_instance thread_run_pre(worker)(struct shared *data, any info) = shared(data);
//@ predicate_family_instance thread_run_post(worker)(struct shared *data, any info) = shared(data);

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct shared *s = malloc(sizeof(struct shared));
    if (s == 0) abort();
    
    //@ close counter_invariant();
    //@ close create_mutex_ghost_arg(counter_invariant);
    s->mtx = create_mutex();
    //@ close shared(s);
    
    struct thread *t = thread_start_joinable(worker, s);
    thread_join(t);
    
    mutex_dispose(s->mtx);
    free(s);
    
    return 0;
}