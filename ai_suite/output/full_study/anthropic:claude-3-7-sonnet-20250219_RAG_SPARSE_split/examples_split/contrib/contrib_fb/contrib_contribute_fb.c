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
box_class contrib_box(int contrib, handle owner) {
    invariant true;

    action set_value(int contrib0);
        requires actionHandles == cons(owner, nil);
        ensures contrib == contrib0 && owner == old_owner;

    handle_predicate contrib_handle(int handleContrib) {
        invariant owner == predicateHandle && contrib == handleContrib;
        
        preserved_by set_value(contrib0) {}
    }
}

predicate_ctor sum(struct sum *sumObject, box box1, handle handle1, box box2, handle handle2)() =
    sumObject->sum |-> ?sum &*&
    contrib_handle(handle1, box1, ?contrib1) &*&
    contrib_handle(handle2, box2, sum - contrib1) &*&
    0 <= contrib1 &*& contrib1 <= 1 &*&
    0 <= sum - contrib1 &*& sum - contrib1 <= 1;

inductive contribute_info = contribute_info(box, handle, box, handle, box, struct sum *, struct lock *);

predicate_family_instance thread_run_pre(contribute)(struct session *session, contribute_info info) =
    switch (info) {
        case contribute_info(box1, handle1, box2, handle2, thisBox, sumObject, lock):
            return contribute_pre(session, box1, handle1, box2, handle2, thisBox, sumObject, lock);
    };

predicate contribute_pre(struct session *session, box box1, handle handle1, box box2, handle handle2, box thisBox, struct sum *sumObject, struct lock *lock) =
    session->sum_object |-> sumObject &*& session->lock |-> lock &*&
    [1/2]lock(lock, _, sum(sumObject, box1, handle1, box2, handle2)) &*& (thisBox == box1 || thisBox == box2) &*& contrib_box(thisBox, 0, _);

predicate_family_instance thread_run_post(contribute)(struct session *session, contribute_info info) =
    switch (info) {
        case contribute_info(box1, handle1, box2, handle2, thisBox, sumObject, lock):
            return [1/2]lock(lock, _, sum(sumObject, box1, handle1, box2, handle2)) &*& contrib_box(thisBox, 1, _);
    };

@*/


void contribute(void *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(contribute)(data, ?info) &*& lockset(currentThread, nil);
    //@ ensures thread_run_post(contribute)(data, info) &*& lockset(currentThread, nil);
{
    struct session *session = data;
    struct lock *lock = session->lock;
    struct sum *sumObject = session->sum_object;
    //@ open thread_run_pre(contribute)(data, info);
    //@ contribute_info box1 = info;
    //@ handle handle1 = box1.handle1;
    //@ box box2 = box1.box2;
    //@ handle handle2 = box1.handle2;
    //@ box thisBox = box1.thisBox;
    //@ open contribute_pre(session, box1, handle1, box2, handle2, thisBox, sumObject, lock);
    free(session);
    lock_acquire(lock);
    //@ open sum(sumObject, box1, handle1, box2, handle2)();
    {
        int sum = sumObject->sum;
        //@ handle owner;
        //@ if (thisBox == box1) owner = handle1; else owner = handle2;
        /*@
        consuming_box_predicate contrib_box(thisBox, ?contrib, ?old_owner)
        perform_action set_value(1) {
        }
        producing_box_predicate contrib_box(thisBox, 1, old_owner);
        @*/
        sumObject->sum = sum + 1;
    }
    //@ close sum(sumObject, box1, handle1, box2, handle2)();
    lock_release(lock);
    //@ close thread_run_post(contribute)(data, info);
}