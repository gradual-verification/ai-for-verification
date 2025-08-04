#include "stdlib.hh"
#include "threading.h"

// A simple reader-writer lock implementation
struct rwlock {
    struct mutex *mutex;
    int readers;
};

/*@

predicate_ctor rwlock_inv(struct rwlock *l)() =
    l->readers |-> ?r &*& 0 <= r &*& r <= INT_MAX;

predicate rwlock(struct rwlock *l) =
    l->mutex |-> ?m &*&
    malloc_block_rwlock(l) &*&
    mutex(m, rwlock_inv(l));

predicate_family_instance thread_run_data(reader)(void *data) =
    [_]((struct rwlock *)data)->mutex |-> ?m &*&
    [_]malloc_block_rwlock((struct rwlock *)data) &*&
    [_]mutex(m, rwlock_inv((struct rwlock *)data));

predicate_family_instance thread_run_data(writer)(void *data) =
    [_]((struct rwlock *)data)->mutex |-> ?m &*&
    [_]malloc_block_rwlock((struct rwlock *)data) &*&
    [_]mutex(m, rwlock_inv((struct rwlock *)data));

@*/

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
    //@ close rwlock_inv(l)();
    //@ close create_mutex_ghost_arg(rwlock_inv(l));
    l->mutex = create_mutex();
    //@ close rwlock(l);
    return l;
}

/***
 * Description:
 * The `reader` function acquires shared access by using the reader-writer lock. 
 * It first increments the number of readers, and then decrements it after the critical section (using mutex).
 *
 * @param l: the reader-writer lock to be used, which has the mutex and has number of readers >= 0
 * 
 */
void reader(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(reader)(l) &*& lockset(currentThread, nil);
    //@ ensures lockset(currentThread, nil);
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

/***
 * Description:
 * The `writer` function acquires exclusive access by using the reader-writer lock. 
 * It waits until there are no readers before entering the critical section.
 *
 * @param l: the reader-writer lock to be used, which has the mutex and has number of readers >= 0
 * 
 */
void writer(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(writer)(l) &*& lockset(currentThread, nil);
    //@ ensures lockset(currentThread, nil);
{
    //@ open thread_run_data(writer)(l);
    for (;;)
        //@ invariant [_]l->mutex |-> ?m &*& [_]mutex(m, rwlock_inv(l));
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

// TODO: make this function pass the verification
/***
 * Description:
 * The `main` function initializes a reader-writer lock and starts a reader and a writer thread.
 */
int main() //@ : main
{
    struct rwlock *l = rwlock_init();

    //@ open rwlock(l);
    //@ leak l->mutex |-> ?m &*& malloc_block_rwlock(l) &*& mutex(m, rwlock_inv(l));

    //@ close thread_run_data(reader)(l);
    thread_start(reader, l);
    
    //@ close thread_run_data(writer)(l);
    thread_start(writer, l);

    return 0;
}