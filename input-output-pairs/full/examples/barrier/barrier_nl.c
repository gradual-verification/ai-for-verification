#include "stdlib.h"
#include "threading.h"
#include <stdbool.h>

/***
 * Description:
 * A barrier is a synchronization mechanism that allows multiple threads
 * to wait until they have all reached the same point of execution.
 * 
 * The structure holds:
 *  - A mutex to ensure mutual exclusion when accessing shared variables.
 *  - The total number of threads (n) that must arrive at the barrier.
 *  - A counter (k) to keep track of how many threads have arrived.
 *  - A boolean (outgoing) to indicate whether threads are being released
 *    from the barrier or are still arriving.
 */
struct barrier {
    struct mutex *mutex;
    int n;
    int k;
    bool outgoing;
};

/***
 * Description:
 * Creates and initializes a new barrier intended for `n` threads.
 *
 * @param n - The number of threads to synchronize with this barrier.
 * @returns A pointer to a newly allocated and initialized `struct barrier`.
 *
 * The function allocates memory for the barrier, sets all fields to default
 * values, and creates a mutex to protect updates to the barrier. If memory 
 * allocation fails, the program calls `abort()`.
 */
struct barrier *create_barrier(int n)
{
    struct barrier *b = malloc(sizeof(struct barrier));
    if (b == 0) abort();

    b->n = n;
    b->k = 0;
    b->outgoing = false;

    b->mutex = create_mutex();
    return b;
}

/***
 * Description:
 * Waits at the barrier until all `n` threads have arrived. Once all have 
 * arrived, the barrier transitions to release them. After the last thread 
 * leaves, the barrier is reset.
 *
 * @param b - A pointer to the `struct barrier` on which to wait.
 *
 * This function uses a mutex to coordinate increments of the arrival counter 
 * (`k`) and to handle the barrier’s `outgoing` flag. Threads spin inside 
 * critical sections (by releasing and reacquiring the mutex) until the 
 * barrier state changes appropriately.
 */
void wait_barrier(struct barrier *b)
{
    mutex_acquire(b->mutex);

    while (b->outgoing) {
        mutex_release(b->mutex);
        mutex_acquire(b->mutex);
    }

    b->k++;
    if (b->k == b->n) {
       
        b->outgoing = true;
        b->k--;
        mutex_release(b->mutex);
    } else {
      
        while (!b->outgoing) {
            mutex_release(b->mutex);
            mutex_acquire(b->mutex);
        }

        b->k--;
        if (b->k == 0) {
   
            b->outgoing = false;
        }
        mutex_release(b->mutex);
    }
}

/***
 * Description:
 * Cleans up and deallocates the barrier once it is no longer needed.
 *
 * @param b - A pointer to the `struct barrier` to dispose of.
 *
 * The function disposes the underlying mutex and frees the memory
 * allocated for the barrier. After calling this function, the barrier
 * pointer must not be used again.
 */
void dispose_barrier(struct barrier *b)
{
    mutex_dispose(b->mutex);
    free(b);
}

/***
 * Description:
 * This structure holds shared data used by two threads that coordinate 
 * via the barrier. The fields `x1`, `x2`, `y1`, `y2`, and `i` are used 
 * as example variables manipulated by the threads.
 */
struct data {
    struct barrier *barrier;
    int x1;
    int x2;
    int y1;
    int y2;
    int i;
};

/***
 * Description:
 * The first worker thread function. It repeatedly uses the barrier to
 * coordinate with the other thread while manipulating the fields `x1`,
 * `x2`, `y1`, and `y2` in the shared `struct data`.
 *
 * @param d - A pointer to the shared `struct data`.
 *
 * The thread checks boundaries on `x1` and `x2`, updates `y1` based on 
 * calculations, then waits at the barrier. It continues updating and 
 * synchronizing until it finishes its loop, then sets `d->i` to 0 before
 * returning.
 */
void thread1(struct data *d)
{
    struct barrier *b = d->barrier;
    wait_barrier(b);

    int N = 0;
    while (N < 30) {
        int a1 = d->x1;
        int a2 = d->x2;
        
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {
            abort();
        }

        d->y1 = a1 + 2 * a2;

        wait_barrier(b);

        a1 = d->y1;
        a2 = d->y2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {
            abort();
        }

        d->x1 = a1 + 2 * a2;

        N++;
        d->i = N;

        wait_barrier(b);
    }

    wait_barrier(b);
    d->i = 0;
}

/***
 * Description:
 * The second worker thread function. It performs similar operations 
 * to `thread1` but with different internal calculations on `x1`, `x2`, 
 * `y1`, and `y2`, also repeatedly waiting at the same barrier to stay 
 * in sync with the first thread.
 *
 * @param d - A pointer to the shared `struct data`.
 */
void thread2(struct data *d)
{
    struct barrier *b = d->barrier;

    wait_barrier(b);

    int m = 0;
    while (m < 30) {
        int a1 = d->x1;
        int a2 = d->x2;

        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {
            abort();
        }

        d->y2 = a1 + 3 * a2;

        wait_barrier(b);

        a1 = d->y1;
        a2 = d->y2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {
            abort();
        }

        d->x2 = a1 + 3 * a2;

        wait_barrier(b);

        m = d->i;
    }

    wait_barrier(b);
}

/***
 * Description:
 * The main function sets up the shared data and barrier, starts two threads
 * (`thread1` and `thread2`) to demonstrate coordination via the barrier, and 
 * then waits for both to finish. Finally, it disposes of the barrier and 
 * frees the shared data.
 *
 * @returns 0 on successful completion of both threads.
 *
 * If any allocation fails, the process calls `abort()`.
 */
int main()
{
    struct data *d = calloc(1, sizeof(struct data));

    struct barrier *b = create_barrier(2);
    d->barrier = b;

    struct thread *t1 = thread_start_joinable(thread1, d);
    struct thread *t2 = thread_start_joinable(thread2, d);

    thread_join(t1);
    thread_join(t2);

    dispose_barrier(d->barrier);
    free(d);

    return 0;
}
