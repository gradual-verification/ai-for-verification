#include "stdlib.h"
#include "threading.h"

struct sum {
    int sum;
    //@ int contrib1;
    //@ int contrib2;
};

struct session {
    struct sum *sum_object;
    struct lock *lock;
};

/*@

// The lock invariant. It protects the physical 'sum' field and holds
// half the permission for the ghost 'contrib' fields.
// The invariant is that the physical sum is the sum of the ghost contributions.
predicate_ctor sum_inv(struct sum *s)() =
    s->sum |-> ?v &*&
    [1/2]s->contrib1 |-> ?c1 &*&
    [1/2]s->contrib2 |-> ?c2 &*&
    v == c1 + c2 &*&
    malloc_block_sum(s);

// Information passed to/from the thread via the 'thread' predicate.
// It contains pointers to the shared objects and a flag to distinguish threads.
inductive contrib_info = contrib_info(struct sum *s, struct lock *l, bool is_first);

// Pre-condition for the 'contribute' thread function.
// It requires ownership of the session data structure, a fraction of the lock,
// and a fraction of the corresponding ghost contribution field.
predicate_family_instance thread_run_pre(contribute)(void *data, contrib_info info) =
    switch (info) {
        case contrib_info(s, l, is_first):
            return
                let session = (struct session *)data;
                session->sum_object |-> s &*&
                session->lock |-> l &*&
                malloc_block_session(session) &*&
                [1/2]lock(l, ?lockId, sum_inv(s)) &*&
                lock_below_all(lockId, nil) == true &*&
                (is_first ? [1/2]s->contrib1 |-> 0 : [1/2]s->contrib2 |-> 0);
    };

// Post-condition for the 'contribute' thread function.
// The session object has been freed. The thread returns its fraction of the lock
// and its fraction of the ghost contribution field, which has now been updated.
predicate_family_instance thread_run_post(contribute)(void *data, contrib_info info) =
    switch (info) {
        case contrib_info(s, l, is_first):
            return
                [1/2]lock(l, ?lockId, sum_inv(s)) &*&
                (is_first ? [1/2]s->contrib1 |-> 1 : [1/2]s->contrib2 |-> 1);
    };

@*/

/*contribute() function
-params: void *data
-description: takes a session object, frees the session object, acquires the lock, increments the sum field of the sum object by 1, releases the lock. 

It requires the data object is a session with its sum_object and lock, and the current thread is one of the two that can modify sum, 
and the current thread hasn't modified the object. 
It ensures that the current thread has done the contribution on adding the sum.
*/
void contribute(void *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(contribute)(data, ?info) &*& lockset(currentThread, nil);
    //@ ensures thread_run_post(contribute)(data, info) &*& lockset(currentThread, nil);
{
    //@ open thread_run_pre(contribute)(data, info);
    //@ switch(info) { case contrib_info(sumObject_info, lock_info, is_first): }
    struct session *session = data;
    struct lock *lock = session->lock;
    struct sum *sumObject = session->sum_object;
    free(session);
    
    lock_acquire(lock);
    //@ open sum_inv(sumObject)();
    
    //@ if (is_first) {
    //@     assert sumObject->contrib1 |-> 0;
    //@     sumObject->contrib1 = 1;
    //@ } else {
    //@     assert sumObject->contrib2 |-> 0;
    //@     sumObject->contrib2 = 1;
    //@ }
   
    {
        int sum = sumObject->sum;
        sumObject->sum = sum + 1;
    }
        
    //@ close sum_inv(sumObject)();
    lock_release(lock);
    
    //@ close thread_run_post(contribute)(data, info);
}


// TODO: make this function pass the verification
/*main() function
-params: none
-description: creates a sum object and a lock object, creates two sessions with the sum object and lock object, creates two threads with the contribute function and the two sessions, joins the first thread, joins the second thread, disposes the lock object, checks if the sum object's sum field is 2, frees the sum object
*/
int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct sum *sumObject = malloc(sizeof(struct sum));
    if (sumObject == 0) {
        abort();
    }
    sumObject->sum = 0;
    //@ sumObject->contrib1 = 0;
    //@ sumObject->contrib2 = 0;
    
    // The lock invariant will take half the permission of the ghost fields.
    // The other half will be passed to the threads.
    //@ close sum_inv(sumObject)();
    //@ close create_lock_ghost_args(sum_inv(sumObject), nil, nil);
    struct lock *lock = create_lock();
    
    struct session *session1 = malloc(sizeof(struct session));
    if (session1 == 0) {
        abort();
    }
    session1->sum_object = sumObject;
    session1->lock = lock;
    //@ close thread_run_pre(contribute)(session1, contrib_info(sumObject, lock, true));
    struct thread *thread1 = thread_start_joinable(contribute, session1);
    
    struct session *session2 = malloc(sizeof(struct session));
    if (session2 == 0) {
        abort();
    }
    session2->sum_object = sumObject;
    session2->lock = lock;
    //@ close thread_run_pre(contribute)(session2, contrib_info(sumObject, lock, false));
    struct thread *thread2 = thread_start_joinable(contribute, session2);
    
    thread_join(thread1);
    //@ open thread_run_post(contribute)(session1, contrib_info(sumObject, lock, true));
    
    thread_join(thread2);
    //@ open thread_run_post(contribute)(session2, contrib_info(sumObject, lock, false));
    
    lock_dispose(lock);
    //@ open sum_inv(sumObject)();
    
    // After disposing the lock and joining the threads, we have full permission
    // for all fields and can check the final state.
    //@ assert sumObject->contrib1 |-> 1;
    //@ assert sumObject->contrib2 |-> 1;
    
    int sum = sumObject->sum;
    assert(sum == 2);
    free(sumObject);

    return 0;
}