#include "stdlib.h"
#include "threading.h"

/***
 * Struct: philosopher
 *
 * Description:
 * Represents a philosopher, each of whom requires access to two locks (forks).
 * Each philosopher operates independently in its own thread.
 */
struct philosopher {
    struct lock *fork1;
    struct lock *fork2;
};


// TODO: make this function pass the verification
/***
 * Function: philosopher_run
 *
 * Description:
 * The function executed by each philosopher thread.
 * In an infinite loop, the philosopher attempts to acquire both forks,
 * and then releases them. This simulates repeated actions (e.g., "eating").
 *
 * Note: This implementation does not prevent deadlock, since multiple philosophers
 * may attempt to acquire overlapping forks in conflicting orders.
 *
@param data - a pointer to the philosopher struct passed at thread start.
 */
void philosopher_run(void *data)
{
    struct philosopher *philosopher = data;
    struct lock *fork1 = philosopher->fork1;
    struct lock *fork2 = philosopher->fork2;
    while (true)
    {
        lock_acquire(fork2);
        lock_acquire(fork1);
        lock_release(fork2);
        lock_release(fork1);
    }
}

