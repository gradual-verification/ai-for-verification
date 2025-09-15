#include "stdlib.h"
#include "threading.h"

// A simple reader-writer lock implementation
struct rwlock {
    struct mutex *mutex;
    int readers;
};

/*@

predicate rwlock_inv(struct rwlock *l) =
    l->readers |-> ?r &*& 0 <= r;

predicate rwlock(struct rwlock *l) =
    l->mutex |-> ?m &*&
    malloc_block_rwlock(l) &*&
    mutex(m, rwlock_inv(l));

@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `rwlock_init` function creates a new reader-writer lock with no reader.
 *
 * The function ensures that the returned value is a reader-writer lock.
 */
struct rwlock *rwlock_init()
    //@ requires true;
    //@ ensures rwlock(result);
{
    struct rwlock *l = malloc(sizeof(struct rwlock));
    if (l == 0) abort();
    l->readers = 0;
    //@ close rwlock_inv(l);
    //@ close create_mutex_ghost_arg(rwlock_inv(l));
    l->mutex = create_mutex();
    //@ close rwlock(l);
    return l;
}