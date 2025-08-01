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

