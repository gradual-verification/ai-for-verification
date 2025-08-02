#include "stdlib.h"

struct thread;

/***
 * Description:
 * The `thread_start` function creates a new thread and starts executing the given function (`run`)
 * with the provided data. It doesn't have an implementation. 
 *
 * @param run - A pointer to the function to execute in the thread.
 * @param data - A pointer to the data required by the thread function.
 *
 */
/*@
predicate_family thread_run_data(void *thread_run)(void *data);

predicate thread(struct thread *t, void *run, void *data);
@*/
struct thread *thread_start(void *run, void *data);
//@ requires is_thread_run(run) == true &*& thread_run_data(run)(data);
//@ ensures thread(result, run, data);


/***
 * Description:
 * The `thread_join` function waits for a given thread to finish execution. It doesn't have an implementation. 
 *
 * @param thread - A pointer to the thread to join.
 *
 * The function blocks the calling thread until the specified thread completes its execution.
 */
void thread_join(struct thread *thread);
//@ requires thread(thread, ?run, ?data);
//@ ensures thread_run_post_join(run)(data);


/**
 * Description:
 * The `increment` function increments the value stored at the memory location pointed to by `cell`.
 *
 * @param cell - A pointer to an integer.
 *
 * The function retrieves the integer value at `cell`, increments it by 1, and stores the result back
 * in the same memory location.
 */
/*@
predicate_family_instance thread_run_data(increment)(void *data) = 
    integer(data, ?v) &*& v < INT_MAX;

predicate_family thread_run_post_join(void *thread_run)(void *data);
predicate_family_instance thread_run_post_join(increment)(void *data) = 
    integer(data, ?v);
@*/
void increment(int *cell) //@ : thread_run
//@ requires thread_run_data(increment)(cell);
//@ ensures thread_run_post_join(increment)(cell);
{
    (*cell)++;
}


/***
 * Description:
 * The `read_int` function reads an integer value from an unspecified source.
 *
 * @returns An integer value.
 *
 * This is a placeholder function for reading an integer. Its implementation may vary depending on
 * the program's requirements.
 */
int read_int();
//@ requires true;
//@ ensures true;


// TODO: make this function pass the verification
/***
* Description:
* The main function demonstrates multithreaded programming by creating a thread to increment an integer value.
*
* 1. Allocates memory for an integer and assigns it a value read from input.
* 2. Starts a thread to increment the value.
* 3. Waits for the thread to complete execution.
* 4. Verifies that the value has been incremented as expected.
* 5. Frees the allocated memory.
*/
int main()
//@ requires true;
//@ ensures true;
{
    int *cell = malloc(sizeof(int));
    if (cell == 0) abort();
    int n = read_int();
    if (n >= INT_MAX) {
        abort();
    }
    *cell = n;
    
    //@ close thread_run_data(increment)(cell);
    struct thread *t = thread_start(increment, cell);
    thread_join(t);
    //@ open thread_run_post_join(increment)(cell);
    int n1 = *cell;
    free(cell);
    assert(n1 == n + 1);
    return 0;
}