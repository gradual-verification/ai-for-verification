#include "stdlib.h"
#include "threading.h"
//@ #include "list.gh"

struct rwlock {
    struct mutex *mutex;
    int readers;
    //@ list<int> active_readers;
};

/*@
predicate_ctor rwlock_inv(struct rwlock *l)() =
    l->readers |-> ?r &*&
    l->active_readers |-> ?ar &*&
    distinct(ar) == true &*&
    r == length(ar) &*&
    malloc_block_rwlock(l);

predicate_family_instance thread_run_data(reader)(struct rwlock *l) =
    [1/2]l->mutex |-> ?m &*& [1/2]mutex(m, rwlock_inv(l));

predicate_family_instance thread_run_data(writer)(struct rwlock *l) =
    [1/2]l->mutex |-> ?m &*& [1/2]mutex(m, rwlock_inv(l));
@*/

struct rwlock *rwlock_init()
    //@ requires true;
    //@ ensures result->mutex |-> ?m &*& mutex(m, rwlock_inv(result));
{
    struct rwlock *l = malloc(sizeof(struct rwlock));
    if (l == 0) abort();
    l->readers = 0;
    //@ l->active_readers = nil;
    //@ close rwlock_inv(l)();
    //@ close create_mutex_ghost_arg(rwlock_inv(l));
    l->mutex = create_mutex();
    return l;
}

void reader(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(reader)(l);
    //@ ensures true;
{
    //@ open thread_run_data(reader)(l);
    //@ struct mutex *m = l->mutex;
    //@ int threadId = currentThread;

    mutex_acquire(l->mutex);
    //@ open rwlock_inv(l)();
    //@ assert l->active_readers |-> ?ar;
    //@ assert !mem(threadId, ar);

    if (l->readers == INT_MAX) {
        //@ close rwlock_inv(l)();
        mutex_release(l->mutex);
        abort();
    }
    l->readers++;
    //@ l->active_readers = cons(threadId, ar);
    //@ close rwlock_inv(l)();
    mutex_release(l->mutex);

    // critical section (reading)

    mutex_acquire(l->mutex);
    //@ open rwlock_inv(l)();
    //@ assert l->active_readers |-> ?ar2;
    //@ mem_remove_eq(threadId, ar2);
    //@ length_remove(threadId, ar2);
    if (l->readers == 0) {
        // This path is now unreachable.
        // Proof: mem(threadId, ar2) is true, so length(ar2) > 0.
        // Since l->readers == length(ar2), l->readers > 0.
        //@ close rwlock_inv(l)();
        mutex_release(l->mutex);
        abort();
    }
    l->readers--;
    //@ l->active_readers = remove(threadId, ar2);
    //@ close rwlock_inv(l)();
    mutex_release(l->mutex);
}

void writer(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(writer)(l);
    //@ ensures true;
{
    //@ open thread_run_data(writer)(l);
    //@ struct mutex *m = l->mutex;
    for (;;)
        //@ invariant [1/2]mutex(m, rwlock_inv(l));
    {
        mutex_acquire(l->mutex);
        //@ open rwlock_inv(l)();
        if (l->readers == 0) {
            //@ assert l->active_readers |-> {nil};
            break;
        }
        //@ close rwlock_inv(l)();
        mutex_release(l->mutex);
    }

    // critical section (writing)

    //@ close rwlock_inv(l)();
    mutex_release(l->mutex);
}

// TODO: make this function pass the verification
int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct rwlock *l = rwlock_init();

    //@ close thread_run_data(reader)(l);
    thread_start(reader, l);
    //@ close thread_run_data(writer)(l);
    thread_start(writer, l);

    return 0;
}