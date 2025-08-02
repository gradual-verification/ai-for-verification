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

predicate_ctor sum_object(struct sum *sumObject)() =
    integer(&sumObject->sum, ?v);

predicate session(struct session *session, struct sum *sumObject, struct lock *lock) =
    session->sum_object |-> sumObject &*& session->lock |-> lock &*& malloc_block_session(session);

predicate_family_instance thread_run_pre(contribute)(struct session *session) =
    [1/2]session(session, ?sumObject, ?lock) &*&
    [1/2]lock(lock, sum_object(sumObject)) &*&
    integer(&sumObject->sum, ?v);

predicate_family_instance thread_run_post(contribute)(struct session *session) =
    [1/2]session(session, ?sumObject, ?lock) &*&
    [1/2]lock(lock, sum_object(sumObject)) &*&
    integer(&sumObject->sum, ?v + 1);

@*/

/*contribute() function
-params: void *data
-description: takes a session object, frees the session object, acquires the lock, increments the sum field of the sum object by 1, releases the lock. 
*/
void contribute(void *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(contribute)(data);
    //@ ensures thread_run_post(contribute)(data);
{
    struct session *session = data;
    //@ open thread_run_pre(contribute)(session);
    struct lock *lock = session->lock;
    struct sum *sumObject = session->sum_object;
    free(session);
    lock_acquire(lock);
    //@ open sum_object(sumObject)();
    {
        int sum = sumObject->sum;
        sumObject->sum = sum + 1;
    }
    //@ close sum_object(sumObject)();
    lock_release(lock);
    //@ close thread_run_post(contribute)(session);
}

// TODO: make this function pass the verification
/*main() function
-params: none
-description: creates a sum object and a lock object, creates two sessions with the sum object and lock object, creates two threads with the contribute function and the two sessions, joins the first thread, joins the second thread, disposes the lock object, checks if the sum object's sum field is 2, frees the sum object
*/
int main()
    //@ requires true;
    //@ ensures true;
{
    struct sum *sumObject = malloc(sizeof(struct sum));
    if (sumObject == 0) {
        abort();
    }
    sumObject->sum = 0;
    //@ close sum_object(sumObject)();
    //@ close create_lock_ghost_args(sum_object(sumObject), nil, nil);
    struct lock *lock = create_lock();
    
    struct session *session1 = malloc(sizeof(struct session));
    if (session1 == 0) {
        abort();
    }
    session1->sum_object = sumObject;
    session1->lock = lock;
    //@ close session(session1, sumObject, lock);
    //@ close thread_run_pre(contribute)(session1);
    struct thread *thread1 = thread_start_joinable(contribute, session1);
    
    struct session *session2 = malloc(sizeof(struct session));
    if (session2 == 0) {
        abort();
    }
    session2->sum_object = sumObject;
    session2->lock = lock;
    //@ close session(session2, sumObject, lock);
    //@ close thread_run_pre(contribute)(session2);
    struct thread *thread2 = thread_start_joinable(contribute, session2);
    
    thread_join(thread1);
    //@ open thread_run_post(contribute)(session1);
    
    thread_join(thread2);
    //@ open thread_run_post(contribute)(session2);
    
    lock_dispose(lock);
    
    int sum = sumObject->sum;
    assert(sum == 2);
    //@ open sum_object(sumObject)();
    free(sumObject);

    return 0;
}