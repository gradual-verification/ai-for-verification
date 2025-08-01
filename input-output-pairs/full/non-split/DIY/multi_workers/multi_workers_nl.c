#include "stdlib.h"
#include "malloc.h"
#include "threading.h"

#define NUM 3

static int counter = 0;


struct shared {
    struct mutex *mtx;
};

// TODO: make this function pass the verification
/***
 * Description:
 * The `worker` function acquires exclusive access and increments the counter.
 *
 * @param data: the shared data structure containing the mutex
 * 
 * It requires and ensures that that the counter is non-negative.
 */
void worker(struct shared *data) //@ : thread_run_joinable
{
    struct shared *s = data;
    mutex_acquire(s->mtx);
    
    int tmp = counter;
    if (tmp == INT_MAX) {
        abort();
    }
    counter = tmp + 1;

    mutex_release(s->mtx);
}

// TODO: make this function pass the verification
/***
 * Description:
 * The `run_workers` function creates a shared data structure, starts multiple worker threads, and waits for them to finish.
 *
 * It requires that counter is initialized to 0 and ensures that the counter is non-negative after all workers have finished.
 */
void run_workers()
{
    struct shared *s = malloc(sizeof(struct shared));
    if (s == 0) abort();
    s->mtx = create_mutex();

    for (int i = 0; i < NUM; i++)
    {
        struct thread *t = thread_start_joinable(worker, s);
        thread_join(t);
    }

    mutex_dispose(s->mtx);
    free(s);
}