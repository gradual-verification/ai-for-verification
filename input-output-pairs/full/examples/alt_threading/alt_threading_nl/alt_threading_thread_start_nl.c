#include "stdlib.h"

struct thread;


// TODO: make this function pass the verification
/***
 * Description:
 * The `thread_start` function creates a new thread and starts executing the given function (`run`)
 * with the provided data. It doesn't have an implementation. 
 *
 * @param run - A pointer to the function to execute in the thread.
 * @param data - A pointer to the data required by the thread function.
 *
 */
struct thread *thread_start(void *run, void *data);

