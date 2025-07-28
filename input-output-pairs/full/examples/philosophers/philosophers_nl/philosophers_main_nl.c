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


/***
 * Function: create_philosopher
 *
 * Description:
 * Allocates and initializes a philosopher with two given forks (locks).
 * Starts a new thread in which the philosopher will run.
 *
@param fork1 - pointer to the first fork (lock) used by the philosopher.
@param fork2 - pointer to the second fork (lock) used by the philosopher.
 */
void create_philosopher(struct lock *fork1, struct lock *fork2)
{
    struct philosopher *philosopher = malloc(sizeof(struct philosopher));
    if (philosopher == 0) abort();
    philosopher->fork1 = fork1;
    philosopher->fork2 = fork2;
    thread_start(philosopher_run, philosopher);
}


// TODO: make this function pass the verification
/***
 * Function: main
 *
 * Description:
 * Initializes three forks (locks) and creates three philosophers.
 * Each philosopher receives a pair of forks that may overlap with other philosophers.
 *
 * This setup demonstrates shared resource contention among threads.
 *
@return 0 on successful completion (though in this case, the threads run indefinitely).
 */
int main()
{
    struct lock *forkA = create_lock();
    struct lock *forkB = create_lock();
    struct lock *forkC = create_lock();
    create_philosopher(forkA, forkB);
    create_philosopher(forkB, forkC);
    create_philosopher(forkA, forkC);
    return 0;
}