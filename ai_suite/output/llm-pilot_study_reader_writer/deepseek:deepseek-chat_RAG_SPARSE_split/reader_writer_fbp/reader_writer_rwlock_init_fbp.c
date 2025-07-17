#include "stdlib.h"
#include "threading.h"

struct rwlock {
    struct mutex *mutex;
    int readers;
};

/*@
predicate_ctor rwlock_inv(struct rwlock *l)() =
    l->readers |-> ?r &*& r >= 0 &*& malloc_block_rwlock(l);

predicate rwlock(struct rwlock *l;) =
    l->mutex |-> ?m &*& mutex(m, rwlock_inv(l));

predicate create_rwlock_ghost_arg() = true;
@*/

struct rwlock *rwlock_init()
    //@ requires create_rwlock_ghost_arg();
    //@ ensures rwlock(result);
{
    struct rwlock *l = malloc(sizeof(struct rwlock));
    if (l == 0) abort();
    l->readers = 0;
    //@ close rwlock_inv(l)();
    //@ close create_mutex_ghost_arg(rwlock_inv(l));
    l->mutex = create_mutex();
    //@ close rwlock(l);
    //@ open create_rwlock_ghost_arg();
    return l;
}