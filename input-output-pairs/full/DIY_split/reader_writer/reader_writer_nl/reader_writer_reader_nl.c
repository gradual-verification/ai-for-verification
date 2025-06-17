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
