#include "stdlib.h"
#include "threading.h"
#include "malloc.h"

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

// TODO: make this function pass the verification
struct rwlock *rwlock_init()
    //@ requires true;
    //@ ensures result->mutex |-> ?m &*& mutex(m, rwlock_inv(result));
{
    struct rwlock *l = malloc(sizeof(struct rwlock));
    if (l == 0) abort();
    l->readers = 0;
    l->mutex = create_mutex();
    //@ close rwlock_inv(l)();
    //@ close create_mutex_ghost_arg(rwlock_inv(l));
    return l;
}

void rwlock_acquire_read(struct rwlock *l)
    //@ requires [1/2]l->mutex |-> ?m &*& [1/2]mutex(m, rwlock_inv(l));
    //@ ensures [1/2]l->mutex |-> m &*& [1/2]mutex(m, rwlock_inv(l)) &*& l->readers |-> ?r &*& r >= 1;
{
    //@ open [1/2]l->mutex |-> m &*& [1/2]mutex(m, rwlock_inv(l));
    mutex_acquire(m);
    l->readers++;
    //@ close rwlock_inv(l)();
    mutex_release(m);
}

void rwlock_release_read(struct rwlock *l)
    //@ requires [1/2]l->mutex |-> ?m &*& [1/2]mutex(m, rwlock_inv(l)) &*& l->readers |-> ?r &*& r >= 1;
    //@ ensures [1/2]l->mutex |-> m &*& [1/2]mutex(m, rwlock_inv(l)) &*& l->readers |-> r - 1;
{
    //@ open [1/2]l->mutex |-> m &*& [1/2]mutex(m, rwlock_inv(l)) &*& l->readers |-> r;
    mutex_acquire(m);
    l->readers--;
    //@ close rwlock_inv(l)();
    mutex_release(m);
}

void rwlock_acquire_write(struct rwlock *l)
    //@ requires [1/2]l->mutex |-> ?m &*& [1/2]mutex(m, rwlock_inv(l));
    //@ ensures [1/2]l->mutex |-> m &*& [1/2]mutex(m, rwlock_inv(l));
{
    //@ open [1/2]l->mutex |-> m &*& [1/2]mutex(m, rwlock_inv(l));
    mutex_acquire(m);
    while (l->readers > 0) {
        // Wait for readers to finish
    }
    //@ close rwlock_inv(l)();
}

void rwlock_release_write(struct rwlock *l)
    //@ requires [1/2]l->mutex |-> ?m &*& [1/2]mutex(m, rwlock_inv(l));
    //@ ensures [1/2]l->mutex |-> m &*& [1/2]mutex(m, rwlock_inv(l));
{
    //@ open [1/2]l->mutex |-> m &*& [1/2]mutex(m, rwlock_inv(l));
    mutex_release(m);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct rwlock *lock = rwlock_init();
    // Example usage of rwlock
    rwlock_acquire_read(lock);
    rwlock_release_read(lock);
    rwlock_acquire_write(lock);
    rwlock_release_write(lock);
    free(lock);
    return 0;
}