#include "stdlib.h"
#include "threading.h"

// A simple reader-writer lock implementation
struct rwlock {
    struct mutex *mutex;
    int readers;
};

//@ predicate rwlock(struct rwlock *l; predicate() p) =
//@     l->mutex |-> ?m &*& l->readers |-> 0 &*& mutex(m, p) &*& malloc_block_rwlock(l);

//@ predicate create_rwlock_ghost_arg(predicate() p) = true;

// TODO: make this function pass the verification
/***
 * Description:
 * The `rwlock_init` function creates a new reader-writer lock with no reader.
 *
 * The function ensures that the returned value is a reader-writer lock.
 */
//@ requires create_rwlock_ghost_arg(?p) &*& p();
//@ ensures result == 0 ? emp : rwlock(result, p);
struct rwlock *rwlock_init()
    //@ requires create_rwlock_ghost_arg(?p) &*& p();
    //@ ensures result == 0 ? emp : rwlock(result, p);
{
    struct rwlock *l = malloc(sizeof(struct rwlock));
    if (l == 0) abort();
    l->readers = 0;
    //@ close create_mutex_ghost_arg(p);
    l->mutex = create_mutex();
    //@ close rwlock(l, p);
    return l;
}