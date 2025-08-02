#include "stdlib.h"
#include "threading.h"

struct sum {
    int sum;
};

struct session {
    struct sum *sum_object;
    struct lock *lock;
};

/*@
// Define a predicate for the sum object
predicate sum_object(struct sum *s; int value) =
    s->sum |-> value &*& malloc_block_sum(s);

// Define a predicate for the lock invariant
predicate_ctor sum_lock_inv(struct sum *s)() =
    sum_object(s, ?value);

// Define a predicate for a session
predicate session(struct session *s; struct sum *sum_obj, struct lock *l) =
    s->sum_object |-> sum_obj &*&
    s->lock |-> l &*&
    malloc_block_session(s);

// Define predicates for thread contribution status
predicate thread_can_contribute(int threadId, struct sum *sum_obj) = true;
predicate thread_has_contributed(int threadId, struct sum *sum_obj) = true;
@*/

// TODO: make this function pass the verification
/*contribute() function
-params: void *data
-description: takes a session object, frees the session object, acquires the lock, increments the sum field of the sum object by 1, releases the lock. 

It requires the data object is a session with its sum_object and lock, and the current thread is one of the two that can modify sum, 
and the current thread hasn't modified the object. 
It ensures that the current thread has done the contribution on adding the sum.
*/
void contribute(void *data) //@ : thread_run_joinable
//@ requires session(data, ?sum_obj, ?lock) &*& [?f]lock(lock, ?lockId, sum_lock_inv(sum_obj)) &*& thread_can_contribute(currentThread, sum_obj);
//@ ensures [f]lock(lock, lockId, sum_lock_inv(sum_obj)) &*& thread_has_contributed(currentThread, sum_obj);
{
    struct session *session = data;
    struct lock *lock = session->lock;
    struct sum *sumObject = session->sum_object;
    //@ open session(session, sum_obj, lock);
    free(session);
    
    lock_acquire(lock);
    //@ open sum_lock_inv(sum_obj)();
    //@ open sum_object(sum_obj, ?old_sum);
    {
        int sum = sumObject->sum;
        sumObject->sum = sum + 1;
    }
    //@ close sum_object(sum_obj, old_sum + 1);
    //@ close sum_lock_inv(sum_obj)();
    lock_release(lock);
    
    //@ close thread_has_contributed(currentThread, sum_obj);
}