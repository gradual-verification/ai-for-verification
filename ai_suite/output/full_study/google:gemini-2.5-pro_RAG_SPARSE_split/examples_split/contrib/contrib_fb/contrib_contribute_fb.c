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
    sumObject->sum |-> ?s &*&
    contrib_handle(handle1, box1, ?contrib1) &*&
    contrib_handle(handle2, box2, s - contrib1) &*&
    0 <= contrib1 &*& contrib1 <= 1 &*&
    0 <= s - contrib1 &*& s - contrib1 <= 1;

inductive contribute_info = contribute_info(box box1, handle handle1, box box2, handle handle2, box thisBox, struct sum *sumObject, struct lock *lock);

predicate_family_instance thread_run_pre(contribute)(struct session *session, contribute_info info) =
    switch (info) {
        case contribute_info(box1, handle1, box2, handle2, thisBox, sumObject, lock):
            return contribute_pre(session, box1, handle1, box2, handle2, thisBox, sumObject, lock);
    };

predicate contribute_pre(struct session *session, box box1, handle handle1, box box2, handle handle2, box thisBox, struct sum *sumObject, struct lock *lock) =
    session->sum_object |-> sumObject &*& session->lock |-> lock &*& malloc_block_session(session) &*&
    [1/2]lock(lock, _, sum(sumObject, box1, handle1, box2, handle2)) &*& (thisBox == box1 || thisBox == box2) &*& contrib_box(thisBox, 0, (thisBox == box1 ? handle1 : handle2));

predicate_family_instance thread_run_post(contribute)(struct session *session, contribute_info info) =
    switch (info) {
        case contribute_info(box1, handle1, box2, handle2, thisBox, sumObject, lock):
            return [1/2]lock(lock, _, sum(sumObject, box1, handle1, box2, handle2)) &*& contrib_box(thisBox, 1, (thisBox == box1 ? handle1 : handle2));
    };

@*/


// TODO: make this function pass the verification
void contribute(void *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(contribute)(data, ?info) &*& lockset(currentThread, nil);
    //@ ensures thread_run_post(contribute)(data, info) &*& lockset(currentThread, nil);
{
    struct session *session = data;
    //@ open thread_run_pre(contribute)(data, info);
    //@ switch (info) { case contribute_info(box1, handle1, box2, handle2, thisBox, sumObject, lock_info):
    //@ open contribute_pre(session, box1, handle1, box2, handle2, thisBox, sumObject, lock_info);

    struct lock *lock = session->lock;
    struct sum *sumObject_ptr = session->sum_object;
    free(session);

    lock_acquire(lock);
    //@ open sum(sumObject_ptr, box1, handle1, box2, handle2)();

    //@ if (thisBox == box1) {
        //@ split_fraction contrib_handle(handle2, box2, _);
        /*@
        consuming_box_predicate contrib_box(thisBox, 0, handle1)
        perform_action set_value(1) {
        @*/
            int sum_val = sumObject_ptr->sum;
            sumObject_ptr->sum = sum_val + 1;
        /*@
        }
        producing_box_predicate contrib_box(thisBox, 1, handle1);
        @*/
        //@ merge_fractions contrib_handle(handle2, box2, _);
    //@ } else {
        //@ split_fraction contrib_handle(handle1, box1, _);
        /*@
        consuming_box_predicate contrib_box(thisBox, 0, handle2)
        perform_action set_value(1) {
        @*/
            int sum_val = sumObject_ptr->sum;
            sumObject_ptr->sum = sum_val + 1;
        /*@
        }
        producing_box_predicate contrib_box(thisBox, 1, handle2);
        @*/
        //@ merge_fractions contrib_handle(handle1, box1, _);
    //@ }

    //@ close sum(sumObject_ptr, box1, handle1, box2, handle2)();
    lock_release(lock);

    //@ close thread_run_post(contribute)(data, info);
    //@ }
}