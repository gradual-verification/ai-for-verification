#include "stdlib.h"

struct thread;


/***
 * Description:
 * The `thread_run` typedef represents a type of function that can be executed by a thread.
 *
 * @param data - A pointer to the data required by the thread function.
 *
 * The function performs operations on the data provided to it. The exact functionality
 * depends on the specific implementation of the thread function.
 */
/*@
  // Define a predicate family for thread_run's precondition
  predicate_family thread_run_pre(void *thread_run)(void *data);
  
  // Define a predicate family for thread_run's postcondition
  predicate_family thread_run_post(void *thread_run)(void *data);
@*/
typedef void thread_run (void *data);
/*@
  // Contract for thread_run function type
  requires thread_run_pre(this)(data);
  ensures thread_run_post(this)(data);
@*/