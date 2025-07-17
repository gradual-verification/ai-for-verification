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
    l->mutex = create_mutex();
    return l;
}

void reader(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(reader)(l);
    //@ ensures true;
{
    mutex_acquire(l->mutex);

    if (l->readers == INT_MAX) {
        abort();
    }
    l->readers++;
    mutex_release(l->mutex);

    // critical section (reading)

    mutex_acquire(l->mutex);
    if (l->readers == 0) {
        abort();
    }
    l->readers--;
    mutex_release(l->mutex);
}

void writer(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(writer)(l);
    //@ ensures true;
{
    for (;;)
    {
        mutex_acquire(l->mutex);
        if (l->readers == 0) {
            break;
        }
        mutex_release(l->mutex);
    }

    // critical section (writing)

    mutex_release(l->mutex);
}

// TODO: make this function pass the verification
int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct rwlock *l = rwlock_init();
    //@ open rwlock_inv(l)();
    //@ close rwlock_inv(l)();

    thread_start(reader, l);
    thread_start(writer, l);

    return 0;
}