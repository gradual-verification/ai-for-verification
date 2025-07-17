#include "stdlib.h"
#include "threading.h"

struct rwlock {
    struct mutex *mutex;
    int readers;
};

/*@
predicate_ctor rwlock_inv(struct rwlock *l)() =
    l->readers |-> ?r &*& r >= 0 &*& malloc_block_rwlock(l);

predicate_family_instance thread_run_data(writer)(struct rwlock *l) =
    [1/2]l->mutex |-> ?m &*& [1/2]mutex(m, rwlock_inv(l));
@*/

// TODO: make this function pass the verification
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

/*@
predicate_family_instance thread_run_data(reader)(struct rwlock *l) =
    [1/2]l->mutex |-> ?m &*& [1/2]mutex(m, rwlock_inv(l));
@*/

// TODO: make this function pass the verification
void reader(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(reader)(l);
    //@ ensures true;
{
    mutex_acquire(l->mutex);
    l->readers++;
    mutex_release(l->mutex);

    // critical section (reading)

    mutex_acquire(l->mutex);
    l->readers--;
    if (l->readers == 0) {
        // Notify writers if needed
    }
    mutex_release(l->mutex);
}

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct rwlock *lock = malloc(sizeof(struct rwlock));
    if (lock == 0) abort();
    lock->readers = 0;
    lock->mutex = create_mutex();

    // Start writer and reader threads
    thread_start(writer, lock);
    thread_start(reader, lock);
    
    // Join threads and cleanup
    // ...

    free(lock);
    return 0;
}