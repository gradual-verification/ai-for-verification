#include "stdlib.h"
#include "threading.h"

// A simple reader-writer lock implementation
struct rwlock {
    struct mutex *mutex;
    int readers;
};

/*@
// Define a predicate for the rwlock invariant
predicate_ctor rwlock_inv(struct rwlock *l)() = 
    l->readers |-> ?r &*& r >= 0;

// Define a predicate for the rwlock
predicate rwlock(struct rwlock *l) = 
    l->mutex |-> ?m &*& 
    mutex(m, rwlock_inv(l)) &*& 
    malloc_block_rwlock(l);

// Define a predicate for when a thread has read access
predicate rwlock_read(struct rwlock *l) = 
    [1/2]l->mutex |-> ?m &*& 
    [1/2]mutex(m, rwlock_inv(l)) &*& 
    [1/2]malloc_block_rwlock(l);

// Define a predicate for when a thread has write access
predicate rwlock_write(struct rwlock *l) = 
    [1/2]l->mutex |-> ?m &*& 
    [1/2]mutex(m, rwlock_inv(l)) &*& 
    [1/2]malloc_block_rwlock(l);

// Thread run data for reader thread
predicate_family_instance thread_run_data(reader)(struct rwlock *l) =
    rwlock_read(l);

// Thread run data for writer thread
predicate_family_instance thread_run_data(writer)(struct rwlock *l) =
    rwlock_write(l);
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
//@ requires thread_run_data(reader)(l);
//@ ensures true;
{
    //@ open thread_run_data(reader)(l);
    //@ open rwlock_read(l);
    struct mutex *mutex = l->mutex;

    mutex_acquire(mutex);
    //@ open rwlock_inv(l)();
    if (l->readers == INT_MAX) {
        abort();
    }
    l->readers++;
    //@ close rwlock_inv(l)();
    mutex_release(mutex);

    // critical section (reading)

    mutex_acquire(mutex);
    //@ open rwlock_inv(l)();
    if (l->readers == 0) {
        abort();
    }
    l->readers--;
    //@ close rwlock_inv(l)();
    mutex_release(mutex);
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
//@ requires thread_run_data(writer)(l);
//@ ensures true;
{
    //@ open thread_run_data(writer)(l);
    //@ open rwlock_write(l);
    struct mutex *mutex = l->mutex;

    for (;;)
    //@ invariant [1/2]mutex(mutex, rwlock_inv(l));
    {
        mutex_acquire(mutex);
        //@ open rwlock_inv(l)();
        if (l->readers == 0) {
            break;
        }
        //@ close rwlock_inv(l)();
        mutex_release(mutex);
    }

    // critical section (writing)

    //@ close rwlock_inv(l)();
    mutex_release(mutex);
}

// TODO: make this function pass the verification
/***
 * Description:
 * The `main` function initializes a reader-writer lock and starts a reader and a writer thread.
 */
int main() //@ : main
//@ requires true;
//@ ensures true;
{
    struct rwlock *l = rwlock_init();
    
    //@ open rwlock(l);
    //@ assert l->mutex |-> ?m;
    //@ assert mutex(m, rwlock_inv(l));
    //@ assert malloc_block_rwlock(l);
    
    //@ close rwlock_read(l);
    //@ close rwlock_write(l);
    
    //@ close thread_run_data(reader)(l);
    thread_start(reader, l);
    
    //@ close thread_run_data(writer)(l);
    thread_start(writer, l);
    
    //@ leak [1/2]l->mutex |-> _ &*& [1/2]mutex(_, _) &*& [1/2]malloc_block_rwlock(l);

    return 0;
}