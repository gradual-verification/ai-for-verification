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
// Define a predicate for the lock invariant
predicate_ctor sum_inv(struct sum *sumObject)() =
    sumObject->sum |-> ?v &*& 
    sumObject->contrib1 |-> ?c1 &*& 
    sumObject->contrib2 |-> ?c2 &*& 
    v == c1 + c2;

// Define thread info for tracking which thread is which
inductive thread_info = thread1 | thread2;

// Define predicates for thread run pre and post conditions
predicate_family_instance thread_run_pre(contribute)(void *data, thread_info info) =
    data != 0 &*&
    ((info == thread1) ?
        [1/2]((struct session *)data)->sum_object |-> ?sumObject &*&
        [1/2]((struct session *)data)->lock |-> ?lock &*&
        [1/4]lock(lock, ?lockId, sum_inv(sumObject)) &*&
        [1/2]sumObject->contrib1 |-> 0 &*&
        malloc_block_session(data)
    :
        [1/2]((struct session *)data)->sum_object |-> ?sumObject &*&
        [1/2]((struct session *)data)->lock |-> ?lock &*&
        [1/4]lock(lock, ?lockId, sum_inv(sumObject)) &*&
        [1/2]sumObject->contrib2 |-> 0 &*&
        malloc_block_session(data)
    );

predicate_family_instance thread_run_post(contribute)(void *data, thread_info info) =
    ((info == thread1) ?
        [1/2]sumObject->contrib1 |-> 1
    :
        [1/2]sumObject->contrib2 |-> 1
    );
@*/

void contribute(void *data) //@ : thread_run_joinable
//@ requires thread_run_pre(contribute)(data, ?info);
//@ ensures thread_run_post(contribute)(data, info);
{
    struct session *session = data;
    struct lock *lock = session->lock;
    struct sum *sumObject = session->sum_object;
    free(session);
    
    lock_acquire(lock);
    //@ open sum_inv(sumObject)();
    {
        int sum = sumObject->sum;
        sumObject->sum = sum + 1;
        
        //@ if (info == thread1) {
        //@     sumObject->contrib1 = 1;
        //@ } else {
        //@     sumObject->contrib2 = 1;
        //@ }
    }
    //@ close sum_inv(sumObject)();
    lock_release(lock);
    
    //@ if (info == thread1) {
    //@     close thread_run_post(contribute)(data, info);
    //@ } else {
    //@     close thread_run_post(contribute)(data, info);
    //@ }
}

int main()
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
    
    //@ close sum_inv(sumObject)();
    //@ close create_lock_ghost_args(sum_inv(sumObject), nil, nil);
    struct lock *lock = create_lock();
    
    struct session *session1 = malloc(sizeof(struct session));
    if (session1 == 0) {
        abort();
    }
    session1->sum_object = sumObject;
    session1->lock = lock;
    
    //@ split_fraction lock_permission(lock, _) by 1/4;
    //@ split_fraction session1_sum_object(session1, _) by 1/2;
    //@ split_fraction session1_lock(session1, _) by 1/2;
    //@ split_fraction sumObject_contrib1(sumObject, _) by 1/2;
    
    //@ close thread_run_pre(contribute)(session1, thread1);
    struct thread *thread1 = thread_start_joinable(contribute, session1);
    
    struct session *session2 = malloc(sizeof(struct session));
    if (session2 == 0) {
        abort();
    }
    session2->sum_object = sumObject;
    session2->lock = lock;
    
    //@ split_fraction lock_permission(lock, _) by 1/3;
    //@ split_fraction session2_sum_object(session2, _) by 1/2;
    //@ split_fraction session2_lock(session2, _) by 1/2;
    //@ split_fraction sumObject_contrib2(sumObject, _) by 1/2;
    
    //@ close thread_run_pre(contribute)(session2, thread2);
    struct thread *thread2 = thread_start_joinable(contribute, session2);
    
    thread_join(thread1);
    //@ open thread_run_post(contribute)(session1, thread1);
    
    thread_join(thread2);
    //@ open thread_run_post(contribute)(session2, thread2);
    
    //@ merge_fractions lock_permission(lock, _);
    lock_dispose(lock);
    
    //@ open sum_inv(sumObject)();
    //@ merge_fractions sumObject_contrib1(sumObject, _);
    //@ merge_fractions sumObject_contrib2(sumObject, _);
    
    int sum = sumObject->sum;
    assert(sum == 2);
    free(sumObject);

    return 0;
}