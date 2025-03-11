// Includes necessary libraries
//@ #include "arrays.gh"
//@ #include "counting.gh"
#include "malloc.h"
#include "stdlib.h"
#include "threading.h"

static int cell;

/*m function
- param data: pointer to data
- description: reads the value of the global variable cell. 
*/
void m(void *data) //@ : thread_run_joinable
{
    int x = cell;
}

/*process function
-param n: number of threads to be created
-descripion: creates n threads that read the value of cell and joins them.

It requires cell points to a value, and n is non-negative. 
It ensures that the value of cell is not changed.
*/
void process(int n)
{
    
    // Allocate memory for thread pointers
    struct thread **threads = malloc(n * sizeof(struct thread *));
    if (threads == 0) abort();

    // Start threads
    for (int i = 0; i < n; i++)
    {
        struct thread *t = thread_start_joinable(m, 0);
        threads[i] = t; // <-- Changed from *(threads + i) = t; to threads[i] = t;
    }
    
    // Join threads
    for (int i = 0; i < n; i++)
    {
        struct thread *t = threads[i]; // <-- Changed from *(threads + i) to threads[i]
        thread_join(t);
    }
    free(threads);
}