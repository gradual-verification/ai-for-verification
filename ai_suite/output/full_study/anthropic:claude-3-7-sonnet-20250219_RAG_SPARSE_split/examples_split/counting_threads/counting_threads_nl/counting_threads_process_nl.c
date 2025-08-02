// Includes necessary libraries
//@ #include "counting.gh"
#include "stdlib.h"
#include "threading.h"

static int cell;

/*@
// Define a predicate to represent access to the cell variable
predicate cell_pred(int value) = cell |-> value;

// Define thread_run_data for the m function
predicate_family_instance thread_run_data(m)(void *data) = 
    [1/2]cell_pred(?value);

// Define thread_run_pre and thread_run_post for the joinable version
predicate_family_instance thread_run_pre(m)(void *data, any info) = 
    [1/2]cell_pred(?value);
predicate_family_instance thread_run_post(m)(void *data, any info) = 
    [1/2]cell_pred(?value);
@*/

/*m function
- param data: pointer to data
- description: reads the value of the global variable cell, making sure that the data is not changed. 
*/
void m(void *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(m)(data, ?info);
    //@ ensures thread_run_post(m)(data, info);
{
    //@ open thread_run_pre(m)(data, info);
    int x = cell;
    //@ close thread_run_post(m)(data, info);
}


// TODO: make this function pass the verification
/*process function
-param n: number of threads to be created
-descripion: creates n threads that read the value of cell and joins them.

It requires that n is non-negative. 
It ensures that the value of cell is not changed.
*/
void process(int n)
    //@ requires n >= 0 &*& cell_pred(?initial_value);
    //@ ensures cell_pred(initial_value);
{
    //@ start_counting(cell_pred, initial_value);
    
    struct thread **threads = malloc(n * sizeof(struct thread *));
    if (threads == 0) abort();
    //@ malloc_block_pointers(threads, n);
    
    for (int i = 0; i < n; i++)
        //@ invariant 0 <= i &*& i <= n &*& malloc_block_pointers(threads, n) &*& pointers(threads, i, ?ps) &*& counting(cell_pred, initial_value, i, initial_value);
    {
        //@ real frac = create_ticket(cell_pred, initial_value);
        //@ close thread_run_pre(m)(0, unit);
        struct thread *t = thread_start_joinable(m, 0);
        threads[i] = t;
    }
    
    for (int i = 0; i < n; i++)
        //@ invariant 0 <= i &*& i <= n &*& malloc_block_pointers(threads, n) &*& pointers(threads, n, ?ps) &*& counting(cell_pred, initial_value, n-i, initial_value);
    {
        struct thread *t = threads[i];
        thread_join(t);
        //@ destroy_ticket(cell_pred, initial_value);
    }
    
    //@ stop_counting(cell_pred, initial_value);
    free(threads);
}