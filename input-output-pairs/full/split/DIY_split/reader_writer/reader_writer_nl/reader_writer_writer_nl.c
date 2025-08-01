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
