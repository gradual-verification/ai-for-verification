// Includes necessary libraries
//@ #include "counting.gh"
#include "stdlib.h"
#include "threading.h"

static int cell;

/*@
// Predicate to hold the thread handle and its associated ghost information.
// In this case, the run function is 'm', data is '0', and the ghost info is 'unit'.
predicate thread_info_m(struct thread *t) = thread(t, m, 0, unit);

// Predicate family instances for the thread run function 'm'.
// These define the pre- and post-conditions for the thread.

// The precondition for thread 'm' requires a ticket for read-only access to 'cell'.
// The ticket provides a fractional permission to the 'integer' predicate for 'cell'.
predicate_family_instance thread_run_pre(m)(void *data, any info) =
    data == 0 &*& info == unit &*&
    ticket(integer, &cell, ?f) &*& [f]integer(&cell, ?v);

// The postcondition for thread 'm' ensures that the ticket and the fractional permission are returned.
// The existential quantifiers allow VeriFast to match this with the state returned by thread_join.
predicate_family_instance thread_run_post(m)(void *data, any info) =
    data == 0 &*& info == unit &*&
    ticket(integer, &cell, ?f) &*& [f]integer(&cell, ?v);
@*/


/*m function
- param data: pointer to data
- description: reads the value of the global variable cell, making sure that the data is not changed. 
*/
void m(void *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(m)(data, ?info);
    //@ ensures thread_run_post(m)(data, info);
{
    //@ open thread_run_pre(m)(data, info);
    int x = cell;
    //@ close thread_run_post(m)(data, info);
}


// TODO: make this function pass the verification
/*process function
-param n: number of threads to be created
-descripion: creates n threads that read the value of cell and joins them.

It requires that n is non-negative. 
It ensures that the value of cell is not changed.
*/
void process(int n)
    //@ requires 0 <= n &*& n < 1000000 &*& integer(&cell, ?v);
    //@ ensures integer(&cell, v);
{
    // Start counting permissions for the shared resource 'cell'.
    // This consumes the full 'integer' predicate and creates a 'counting' predicate.
    //@ start_counting(integer, &cell);
    
    struct thread **threads = malloc(n * sizeof(struct thread *));
    if (threads == 0) abort();
    // Convert the raw character buffer from malloc into a pointers_ predicate.
    //@ chars__to_pointers_(threads, n);

    // Loop to create 'n' threads.
    for (int i = 0; i < n; i++)
        /*@
        invariant 0 <= i &*& i <= n &*&
                  // The counter in 'counting' tracks the number of tickets issued.
                  counting(integer, &cell, i, v) &*&
                  // The 'threads' array is partially initialized.
                  // 'pointers' describes the initialized part.
                  pointers(threads, i, ?tps) &*&
                  // 'foreach' ensures each created thread handle has its 'thread_info_m' predicate.
                  foreach(tps, thread_info_m) &*&
                  // 'pointers_' describes the uninitialized part.
                  pointers_(threads + i, n - i, _) &*&
                  // We must keep the malloc_block for the final free.
                  malloc_block_pointers(threads, n);
        @*/
    {
        // Create a ticket for the new thread, incrementing the counter.
        //@ real f = create_ticket(integer, &cell);
        // The thread's precondition requires the ticket and the fractional permission.
        //@ close thread_run_pre(m)(0, unit);
        struct thread *t = thread_start_joinable(m, 0);
        // The 'thread' predicate is returned by thread_start_joinable. We wrap it in our helper.
        //@ close thread_info_m(t);
        
        // Store the thread handle in the array.
        //@ pointers__split(threads + i, 1);
        threads[i] = t;
        // Join the newly initialized element back into the main 'pointers' predicate.
        //@ pointers_join(threads);
        // Append the new thread's info to the 'foreach' predicate.
        //@ close foreach(cons(t, nil), thread_info_m);
        //@ foreach_append(tps, cons(t, nil));
    }
    
    //@ assert pointers(threads, n, ?tps) &*& foreach(tps, thread_info_m);

    // Loop to join the 'n' threads.
    for (int i = 0; i < n; i++)
        /*@
        invariant 0 <= i &*& i <= n &*&
                  // The counter decreases as we join threads and destroy tickets.
                  counting(integer, &cell, n - i, v) &*&
                  // The 'threads' array is fully initialized.
                  pointers(threads, n, tps) &*&
                  // We only have 'thread_info_m' for the threads not yet joined.
                  foreach(drop(i, tps), thread_info_m) &*&
                  malloc_block_pointers(threads, n);
        @*/
    {
        struct thread *t = threads[i];
        // Separate the head of the list of remaining threads to get the current thread's info.
        //@ drop_n_plus_one(i, tps);
        //@ open foreach(drop(i, tps), thread_info_m);
        //@ open thread_info_m(t);
        thread_join(t);
        // 'thread_join' returns the thread's postcondition.
        //@ open thread_run_post(m)(0, unit);
        // Destroy the ticket, which consumes the ticket and the fraction, and decrements the counter.
        //@ destroy_ticket(integer, &cell);
    }
    
    // Convert the 'pointers' predicate back to 'chars_' to be able to free the memory.
    //@ pointers_to_chars(threads, n);
    //@ chars_to_chars_(threads);
    free(threads);
    
    // Stop counting. This requires the counter to be 0 and returns the full 'integer' predicate.
    //@ stop_counting(integer, &cell);
}