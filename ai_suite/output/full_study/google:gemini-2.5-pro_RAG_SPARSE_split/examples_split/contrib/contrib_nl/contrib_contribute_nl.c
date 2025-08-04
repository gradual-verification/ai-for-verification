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

// A predicate for the sum struct. It is declared as precise (by the semicolon)
// which allows VeriFast to merge fractional permissions of this predicate.
predicate sum_pred(struct sum *s; int val) =
    s->sum |-> val &*& malloc_block_sum(s);

// The lock invariant for the lock protecting the sum object.
// It is a predicate constructor, meaning its value is fixed when the lock is created.
// It states that the lock protects a sum object, but doesn't expose its value.
predicate_ctor sum_inv(struct sum *s)() =
    sum_pred(s, _);

// A predicate for the session struct, also declared as precise.
predicate session_pred(struct session *s; struct sum *sum_obj, struct lock *l) =
    s->sum_object |-> sum_obj &*&
    s->lock |-> l &*&
    malloc_block_session(s);

// A ghost predicate to represent that a thread has completed its contribution.
// This acts as a "receipt" that the main thread can check after joining.
predicate contribution_receipt() = true;

// An inductive datatype to pass information from the thread's precondition
// to its postcondition. This is useful because the 'data' argument (the session)
// is freed inside the thread. It carries the lock's fractional permission value.
inductive cont_info = cont_info(struct sum *sum_obj, struct lock *l, real f);

// Precondition for the 'contribute' thread function.
// It requires ownership of the session object and a fractional permission for the lock.
// The 'info' parameter is used to pass data to the postcondition.
predicate_family_instance thread_run_pre(contribute)(void *data, cont_info info) =
    data == (void*)?s &*&
    session_pred(s, ?sum_obj, ?l) &*&
    [?f]lock(l, ?lockId, sum_inv(sum_obj)) &*&
    info == cont_info(sum_obj, l, f);

// Postcondition for the 'contribute' thread function.
// It returns the lock permission and a 'receipt' of its contribution.
// The session object is gone, as it was freed.
predicate_family_instance thread_run_post(contribute)(void *data, cont_info info) =
    switch(info) {
        case cont_info(sum_obj, l, f):
            return [f]lock(l, _, sum_inv(sum_obj)) &*& contribution_receipt();
    };

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
    //@ requires thread_run_pre(contribute)(data, ?info) &*& lockset(currentThread, nil);
    //@ ensures thread_run_post(contribute)(data, info) &*& lockset(currentThread, nil);
{
    //@ open thread_run_pre(contribute)(data, info);
    struct session *session = data;
    //@ open session_pred(session, ?sumObject_ghost, ?lock_ghost);
    struct lock *lock = session->lock;
    struct sum *sumObject = session->sum_object;
    free(session);
    
    //@ switch(info) { case cont_info(sum_obj, l, f): }
    //@ assert [f]lock(lock, ?lockId, sum_inv(sumObject));
    
    lock_acquire(lock);
    //@ open sum_inv(sumObject)();
    //@ open sum_pred(sumObject, ?v);
   
    {
        int sum = sumObject->sum;
        sumObject->sum = sum + 1;
    }
    
    //@ close sum_pred(sumObject, v + 1);
    //@ close sum_inv(sumObject)();
    lock_release(lock);
    
    //@ close contribution_receipt();
    //@ close thread_run_post(contribute)(data, info);
}