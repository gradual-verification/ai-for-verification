#include "stdlib.h"

struct thread;

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
#include "stdlib.h"

struct thread;

/*@
predicate_family thread_run_pre(void *thread_run)(void *data, any info);
predicate_family thread_run_post(void *thread_run)(void *data, any info);
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