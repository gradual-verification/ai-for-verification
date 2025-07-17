#include "stdlib.hh"
#include "threading.h"

struct rwlock {
    struct mutex *mutex;
    int readers;
};

/*@
predicate_ctor rwlock_inv(struct rwlock *l)() =
    l->readers |-> ?r &*& r >= 0 &*& malloc_block_rwlock(l);
@*/

struct rwlock *rwlock_init()
    //@ requires true;
    //@ ensures result->mutex |-> ?m &*& mutex(m, rwlock_inv(result));
{
    struct rwlock *l = malloc(sizeof(struct rwlock));
    if (l == 0) abort();
    l->readers = 0;
    
    // To create a mutex, we must provide the resources for its invariant.
    // The `malloc` call provides `malloc_block_rwlock(l)`, and we've set `l->readers`.
    // We close the invariant predicate to bundle these resources.
    //@ close rwlock_inv(l)();
    
    // We also need to provide the ghost argument specifying which invariant to use.
    //@ close create_mutex_ghost_arg(rwlock_inv(l));
    
    l->mutex = create_mutex();
    return l;
}
