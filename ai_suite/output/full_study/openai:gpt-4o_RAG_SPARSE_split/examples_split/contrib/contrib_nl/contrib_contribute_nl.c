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

predicate_ctor sum_inv(struct sum *sum_object)() =
    integer(&sum_object->sum, ?v);

predicate session(struct session *session, struct sum *sum_object, struct lock *lock) =
    session->sum_object |-> sum_object &*& session->lock |-> lock &*& malloc_block_session(session);

predicate_family_instance thread_run_pre(contribute)(struct session *session) =
    [1/2]session(session, ?sum_object, ?lock) &*&
    [1/2]lock(lock, sum_inv(sum_object)) &*&
    integer(&sum_object->sum, ?v);

predicate_family_instance thread_run_post(contribute)(struct session *session) =
    [1/2]session(session, ?sum_object, ?lock) &*&
    [1/2]lock(lock, sum_inv(sum_object)) &*&
    integer(&sum_object->sum, ?v + 1);

@*/

// TODO: make this function pass the verification
void contribute(void *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(contribute)(data);
    //@ ensures thread_run_post(contribute)(data);
{
    struct session *session = data;
    struct lock *lock = session->lock;
    struct sum *sumObject = session->sum_object;
    //@ open thread_run_pre(contribute)(session);
    free(session);
    lock_acquire(lock);
    //@ open sum_inv(sumObject)();
    {
        int sum = sumObject->sum;
        sumObject->sum = sum + 1;
    }
    //@ close sum_inv(sumObject)();
    lock_release(lock);
    //@ close thread_run_post(contribute)(session);
}