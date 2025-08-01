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
