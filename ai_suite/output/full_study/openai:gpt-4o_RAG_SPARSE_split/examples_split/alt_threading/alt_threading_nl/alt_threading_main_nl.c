#include "stdlib.h"
#include "threading.h"
#include "limits.h"

struct thread;

/*@
predicate_family thread_run_pre(void *run)(void *data, any info);
predicate_family thread_run_post(void *run)(void *data, any info);

predicate thread(struct thread *thread, void *run, void *data, any info);

predicate_family_instance thread_run_pre(increment)(int *cell, any info) =
    integer(cell, ?n) &*& n < INT_MAX;

predicate_family_instance thread_run_post(increment)(int *cell, any info) =
    integer(cell, ?n) &*& n == old_int(cell) + 1;
@*/

/**
 * Description:
 * The `increment` function increments the value stored at the memory location pointed to by `cell`.
 *
 * @param cell - A pointer to an integer.
 *
 * The function retrieves the integer value at `cell`, increments it by 1, and stores the result back
 * in the same memory location.
 */
void increment(int *cell)
    //@ requires thread_run_pre(increment)(cell, ?info);
    //@ ensures thread_run_post(increment)(cell, info);
{
    //@ open thread_run_pre(increment)(cell, info);
    (*cell)++;
    //@ close thread_run_post(increment)(cell, info);
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

//@ predicate main_pre() = true;
//@ predicate main_post() = true;

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
    //@ requires main_pre();
    //@ ensures main_post();
{
    int *cell = malloc(sizeof(int));
    if (cell == 0) abort();
    int n = read_int();
    if (n >= INT_MAX) {
        abort();
    }
    *cell = n;

    //@ close thread_run_pre(increment)(cell, unit);
    struct thread *t = thread_start(increment, cell);
    //@ open thread(t, increment, cell, unit);
    thread_join(t);
    //@ open thread_run_post(increment)(cell, unit);
    int n1 = *cell;
    free(cell);
    assert(n1 == n + 1);
    return 0;
}