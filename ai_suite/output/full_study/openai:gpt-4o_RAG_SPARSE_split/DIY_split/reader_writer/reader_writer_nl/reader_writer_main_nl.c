#include "stdlib.h"
#include "threading.h"

// A simple reader-writer lock implementation
struct rwlock {
    struct mutex *mutex;
    int readers;
};

/*@

predicate rwlock(struct rwlock *l; int readers) =
    l->mutex |-> ?mutex &*&
    l->readers |-> readers &*&
    mutex(mutex, rwlock_inv(l)) &*&
    readers >= 0;

predicate rwlock_inv(struct rwlock *l)() =
    l->readers |-> ?readers &*&
    readers >= 0;

@*/

/***
 * Description:
 * The `rwlock_init` function creates a new reader-writer lock with no reader.
 *
 * The function ensures that the returned value is a reader-writer lock.
 */
struct rwlock *rwlock_init()
    //@ requires true;
    //@ ensures result != 0 ? rwlock(result, 0) : true;
{
    struct rwlock *l = malloc(sizeof(struct rwlock));
    if (l == 0) abort();
    l->readers = 0;
    //@ close rwlock_inv(l)();
    //@ close create_mutex_ghost_arg(rwlock_inv(l));
    l->mutex = create_mutex();
    //@ close rwlock(l, 0);
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
    //@ requires rwlock(l, ?readers);
    //@ ensures rwlock(l, readers);
{
    //@ open rwlock(l, readers);
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
    //@ close rwlock(l, readers);
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
    //@ requires rwlock(l, ?readers);
    //@ ensures rwlock(l, readers);
{
    for (;;)
    {
        //@ open rwlock(l, readers);
        mutex_acquire(l->mutex);
        //@ open rwlock_inv(l)();
        if (l->readers == 0) {
            break;
        }
        //@ close rwlock_inv(l)();
        mutex_release(l->mutex);
        //@ close rwlock(l, readers);
    }

    // critical section (writing)

    //@ close rwlock_inv(l)();
    mutex_release(l->mutex);
    //@ close rwlock(l, readers);
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
    if (l == 0) abort();

    //@ close thread_run_data(reader)(l);
    thread_start(reader, l);
    //@ close thread_run_data(writer)(l);
    thread_start(writer, l);

    return 0;
}