#include "stdlib.h"
#include "threading.h"

// A simple reader-writer lock implementation
struct rwlock {
    struct mutex *mutex;
    int readers;
};

// TODO: make this function pass the verification
/***
 * Description:
 * The `rwlock_init` function creates a new reader-writer lock with no reader.
 *
 * The function ensures that the returned value is a reader-writer lock.
 */
struct rwlock *rwlock_init()
{
    struct rwlock *l = malloc(sizeof(struct rwlock));
    if (l == 0) abort();
    l->readers = 0;
    l->mutex = create_mutex();
    return l;
}

// TODO: make this function pass the verification
/***
 * Description:
 * The `reader` function acquires shared access by using the reader-writer lock. 
 * It first increments the number of readers, and then decrements it after the critical section (using mutex).
 *
 * @param l: the reader-writer lock to be used, which has the mutex and has number of readers >= 0
 * 
 */
void reader(struct rwlock *l) //@ : thread_run
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

// TODO: make this function pass the verification
/***
 * Description:
 * The `writer` function acquires exclusive access by using the reader-writer lock. 
 * It waits until there are no readers before entering the critical section.
 *
 * @param l: the reader-writer lock to be used, which has the mutex and has number of readers >= 0
 * 
 */
void writer(struct rwlock *l) //@ : thread_run
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
/***
 * Description:
 * The `main` function initializes a reader-writer lock and starts a reader and a writer thread.
 */
int main() //@ : main
{
    struct rwlock *l = rwlock_init();

    thread_start(reader, l);
    thread_start(writer, l);

    return 0;
}