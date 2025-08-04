#include "stdlib.h"

struct thread;

/*@

// A thread's run function is specified by two predicate families,
// one for its precondition and one for its postcondition.
// These predicate families are parameterized by the run function's address,
// allowing each program to define its own run functions with their own contracts.
predicate_family thread_run_pre(void *run)(void *data, any info);
predicate_family thread_run_post(void *run)(void *data, any info);

// The 'thread' predicate represents a handle for a running thread.
// It stores the thread's run function, its argument, and the ghost info
// that is passed from the precondition to the postcondition.
predicate thread(struct thread *thread, void *run, void *data, any info);

@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `thread_join` function waits for a given thread to finish execution. It doesn't have an implementation. 
 *
 * @param thread - A pointer to the thread to join.
 *
 * The function blocks the calling thread until the specified thread completes its execution.
 */
void thread_join(struct thread *thread);
//@ requires thread(thread, ?run, ?data, ?info);
//@ ensures thread_run_post(run)(data, info);
