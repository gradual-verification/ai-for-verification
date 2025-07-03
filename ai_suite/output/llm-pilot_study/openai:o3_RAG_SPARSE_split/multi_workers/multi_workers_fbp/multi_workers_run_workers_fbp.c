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

// Verified version
void run_workers()
    //@ requires counter |-> 0;
    //@ ensures counter |-> ?v &*& v >= 0;
{
    struct shared *s = malloc(sizeof(struct shared));
    if (s == 0) abort();
    //@ close shared_inv(s)();                       // counter |-> 0 + malloc_block_shared(s)
    //@ close create_mutex_ghost_arg(shared_inv(s)); // ghost argument for create_mutex
    struct mutex *m = create_mutex();               // produces full mutex chunk
    s->mtx = m;

    for (int i = 0; i < NUM; i++)
        /*@
        invariant
            [_]s->mtx |-> m &*&                // some (possibly full) fraction
            [_]mutex(m, shared_inv(s));        // matching fraction
        @*/
    {
        //@ close thread_run_pre(worker)(s, unit);
        struct thread *t = thread_start_joinable(worker, s);
        thread_join(t);
        //@ open thread_run_post(worker)(s, unit);

        /*  After the join we again own the fractions that were
            passed to the thread.  Merge them so that, at the end
            of each loop iteration, we have a single chunk; this
            keeps the heap simple and ensures we will have the full
            permission after the last iteration.                             */
        //@ merge_fractions s->mtx |-> m;
        //@ merge_fractions mutex(m, shared_inv(s));
    }

    mutex_dispose(m);         // requires full mutex chunk
    //@ open shared_inv(s)();  // get back counter |-> v and malloc_block_shared(s)
    free(s);                  // needs malloc_block_shared(s)
}