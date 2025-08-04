#include "stdlib.h"

struct thread;

/*@

// An abstract predicate representing the handle to a running thread's future result.
// This token is produced when a thread is started and would be consumed by a join operation.
predicate thread_token(struct thread *t, predicate() post);

// This lemma models the fundamental operation of creating a new thread.
// It consumes the resources required by the new thread's run function ('pre')
// and produces a token representing the thread's future result ('post').
// This is an axiom of the threading model, abstracting over the OS scheduler.
lemma void thread_fork_axiom(void *run, void *data, struct thread *t);
    requires [_]is_thread_run(run, ?pre, ?post) &*& pre(data);
    ensures thread_token(t, post);

// A hypothetical join function would use a corresponding axiom to consume the token
// and produce the postcondition:
// lemma void thread_join_axiom(struct thread *t);
//     requires thread_token(t, ?post);
//     ensures post();

// The contract for the thread handle. It includes the memory block of the handle
// and the abstract token.
predicate thread(struct thread *thread, predicate() post) =
    malloc_block_thread(thread) &*& thread_token(thread, post);

@*/

//@ predicate_ctor integer1(int *cell, int value)(int *cell1) = integer(cell, value) &*& cell1 == cell;
//@ predicate_ctor integer2(int *cell, int value)() = integer(cell, value);


typedef void thread_run/*@(predicate(void *) pre, predicate() post)@*/(void *data);
    //@ requires pre(data);
    //@ ensures post();


// TODO: make this function pass the verification
struct thread *thread_start(void *run, void *data)
    //@ requires [_]is_thread_run(run, ?pre, ?post) &*& pre(data);
    //@ ensures thread(result, post);
{
    struct thread *t = malloc(sizeof(struct thread));
    if (t == 0) {
        abort();
    }
    
    // We model the creation of the new thread by calling our axiom.
    // This consumes the precondition `pre(data)` and produces the `thread_token`.
    thread_fork_axiom(run, data, t);
    
    // Now we have `malloc_block_thread(t)` from malloc
    // and `thread_token(t, post)` from the axiom.
    // We can close the `thread` predicate.
    close thread(t, post);
    
    return t;
}