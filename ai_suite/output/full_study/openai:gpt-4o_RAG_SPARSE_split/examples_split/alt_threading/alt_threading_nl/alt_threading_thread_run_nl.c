#include "stdlib.h"

//@ #include "prelude.h"

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
//@ requires exists<void *>(data);
//@ ensures true;

struct thread;

//@ predicate_family thread_run_pre(void *thread_run)(void *data);
//@ predicate_family thread_run_post(void *thread_run)(void *data);

typedef void thread_run_with_contract(void *data);
//@ requires thread_run_pre(this)(data);
//@ ensures thread_run_post(this)(data);

struct thread *thread_start(thread_run_with_contract *run, void *data);
//@ requires is_thread_run_with_contract(run) == true &*& thread_run_pre(run)(data);
//@ ensures thread(result, run, data);

void thread_join(struct thread *thread);
//@ requires thread(thread, ?run, ?data);
//@ ensures thread_run_post(run)(data);