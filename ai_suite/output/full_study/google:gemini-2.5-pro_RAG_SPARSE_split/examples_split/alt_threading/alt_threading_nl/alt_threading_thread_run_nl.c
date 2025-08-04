#include "stdlib.h"

struct thread;

/*@
// A predicate family to specify the precondition of a thread's run function.
// This allows different thread functions to have different preconditions.
// The family is indexed by the function pointer `run`.
predicate_family thread_run_pre(void *run)(void *data);
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `thread_run` typedef represents a type of function that can be executed by a thread.
 *
 * @param data - A pointer to the data required by the thread function.
 *
 * The function performs operations on the data provided to it. The exact functionality
 * depends on the specific implementation of the thread function.
 */
typedef void thread_run (void *data);
//@ requires thread_run_pre(this)(data);
//@ ensures true;
