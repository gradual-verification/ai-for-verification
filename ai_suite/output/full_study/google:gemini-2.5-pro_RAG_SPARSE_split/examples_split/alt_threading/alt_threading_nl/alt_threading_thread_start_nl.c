#include "stdlib.h"

/*@

// A predicate family for the precondition of a thread's run function.
// It is indexed by the run function's address.
// 'data' is the argument to the run function.
// 'info' is a ghost parameter to pass information from the thread creator to the thread joiner.
predicate_family thread_run_pre(void *run)(void *data, any info);

// A predicate family for the postcondition of a thread's run function.
predicate_family thread_run_post(void *run)(void *data, any info);

// A predicate representing a handle to a running thread.
// It stores the run function, its data, and the ghost info.
predicate thread(struct thread *thread, void *run, void *data, any info);

@*/

// A function pointer type for the function that a thread executes.
typedef void thread_run(void *data);
    //@ requires thread_run_pre(this)(data, ?info);
    //@ ensures thread_run_post(this)(data, info);

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
struct thread *thread_start(void *run, void *data)
    //@ requires is_thread_run(run) == true &*& thread_run_pre(run)(data, ?info);
    //@ ensures thread(result, run, data, info);
;
