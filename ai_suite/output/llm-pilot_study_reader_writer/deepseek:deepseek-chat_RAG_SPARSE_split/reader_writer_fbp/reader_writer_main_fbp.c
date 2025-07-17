#include "stdlib.h"
#include "threading.h"

struct rwlock {
    struct mutex *mutex;
    int readers;
};

/*@
predicate_ctor rwlock_inv(struct rwlock *l)() =
    l->readers |-> ?r &*& r >= 0 &*& malloc_block_rwlock(l);

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
    mutex_acquire(l->mutex);
    //@ open rwlock_inv(l)();

    if (l->readers == INT_MAX) {
        abort();
    }
    l->readers++;
    //@ close rwlock_inv(l)();
    mutex_release(l->mutex);

    // critical section (reading)

    mutex_acquire(l->mutex);
    //@ open rwlock_inv(l)();
    if (l->readers == 0) {
        abort();
    }
    l->readers--;
    //@ close rwlock_inv(l)();
    mutex_release(l->mutex);
}

void writer(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(writer)(l);
    //@ ensures true;
{
    //@ open thread_run_data(writer)(l);
    for (;;)
    {
        mutex_acquire(l->mutex);
        //@ open rwlock_inv(l)();
        if (l->readers == 0) {
            break;
        }
        //@ close rwlock_inv(l)();
        mutex_release(l->mutex);
    }

    // critical section (writing)

    //@ close rwlock_inv(l)();
    mutex_release(l->mutex);
}

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct rwlock *l = rwlock_init();
    
    // Split the mutex into two fractions for the reader and writer threads
    //@ assert l->mutex |-> ?m;
    //@ split_fraction mutex(m, rwlock_inv(l)) by 1/2;
    
    // Create reader thread
    //@ close thread_run_data(reader)(l);
    thread_start(reader, l);
    
    // Create writer thread
    //@ close thread_run_data(writer)(l);
    thread_start(writer, l);

    return 0;
}