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
// MODIFIED SPECIFICATION
box_class contrib_box(int contrib, handle owner) {
    invariant true;

    action set_value(int contrib0);
        requires actionHandles == cons(owner, nil);
        ensures contrib == contrib0 && owner == old_owner;

    handle_predicate contrib_handle(; int handleContrib) {
        invariant owner == predicateHandle && contrib == handleContrib;
        
        preserved_by set_value(contrib0) {
            open contrib_handle();
            close contrib_handle();
        }
    }
}

predicate_ctor sum(struct sum *sumObject, box box1, handle handle1, box box2, handle handle2)() =
    sumObject->sum |-> ?s &*&
    contrib_box(box1, ?c1, handle1) &*& contrib_handle(handle1, box1; c1) &*&
    contrib_box(box2, ?c2, handle2) &*& contrib_handle(handle2, box2; c2) &*&
    s == c1 + c2 &*&
    0 <= c1 &*& c1 <= 1 &*&
    0 <= c2 &*& c2 <= 1;

inductive contribute_info = contribute_info(box, handle, box, handle, box, struct sum *, struct lock *);

predicate_family_instance thread_run_pre(contribute)(struct session *session, contribute_info info) =
    switch (info) {
        case contribute_info(box1, handle1, box2, handle2, thisBox, sumObject, lock):
            return contribute_pre(session, box1, handle1, box2, handle2, thisBox, sumObject, lock);
    };

predicate contribute_pre(struct session *session, box box1, handle handle1, box box2, handle handle2, box thisBox, struct sum *sumObject, struct lock *lock) =
    session->sum_object |-> sumObject &*& session->lock |-> lock &*& malloc_block_session(session) &*&
    [1/2]lock(lock, _, sum(sumObject, box1, handle1, box2, handle2)) &*&
    (thisBox == box1 || thisBox == box2);

predicate_family_instance thread_run_post(contribute)(struct session *session, contribute_info info) =
    switch (info) {
        case contribute_info(box1, handle1, box2, handle2, thisBox, sumObject, lock):
            return [1/2]lock(lock, _, sum(sumObject, box1, handle1, box2, handle2));
    };

@*/


void contribute(void *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(contribute)(data, ?info) &*& lockset(currentThread, nil);
    //@ ensures thread_run_post(contribute)(data, info) &*& lockset(currentThread, nil);
{
    struct session *session = data;
    //@ open thread_run_pre(contribute)(data, info);
    //@ switch(info) { case contribute_info(box1, handle1, box2, handle2, thisBox, sumObject, lock_): }
    //@ open contribute_pre(session, box1, handle1, box2, handle2, thisBox, sumObject, lock_);
    struct lock *lock = session->lock;
    struct sum *sumObject = session->sum_object;
    free(session);
    lock_acquire(lock);
    //@ open sum(sumObject, box1, handle1, box2, handle2)();
    
    /*@
    if (thisBox == box1) {
        consuming_box_predicate contrib_box(box1, ?c1, handle1)
        consuming_handle_predicate contrib_handle(handle1, box1; c1)
        perform_action set_value(1) {
            open contrib_handle();
            close contrib_handle();
        }
        producing_box_predicate contrib_box(box1, 1, handle1)
        producing_handle_predicate contrib_handle(handle1, box1; 1);
    } else {
        consuming_box_predicate contrib_box(box2, ?c2, handle2)
        consuming_handle_predicate contrib_handle(handle2, box2; c2)
        perform_action set_value(1) {
            open contrib_handle();
            close contrib_handle();
        }
        producing_box_predicate contrib_box(box2, 1, handle2)
        producing_handle_predicate contrib_handle(handle2, box2; 1);
    }
    @*/
   
    {
        int sum = sumObject->sum;
        sumObject->sum = sum + 1;
    }
    
    //@ close sum(sumObject, box1, handle1, box2, handle2)();
    lock_release(lock);
    
    //@ close thread_run_post(contribute)(data, info);
}


// TODO: make this function pass the verification
int main()
    //@ requires true;
    //@ ensures true;
{
    struct sum *sumObject = malloc(sizeof(struct sum));
    if (sumObject == 0) {
        abort();
    }
    sumObject->sum = 0;
    
    //@ create_box box1 = contrib_box(0, h1) and_handle h1 = contrib_handle(;0);
    //@ create_box box2 = contrib_box(0, h2) and_handle h2 = contrib_handle(;0);
    
    //@ close sum(sumObject, box1, h1, box2, h2)();
    //@ close create_lock_ghost_args(sum(sumObject, box1, h1, box2, h2), nil, nil);
    struct lock *lock = create_lock();
    
    //@ split_fraction lock(lock, _, _);
    
    struct session *session1 = malloc(sizeof(struct session));
    if (session1 == 0) {
        abort();
    }
    session1->sum_object = sumObject;
    session1->lock = lock;
    //@ close contribute_pre(session1, box1, h1, box2, h2, box1, sumObject, lock);
    //@ close thread_run_pre(contribute)(session1, contribute_info(box1, h1, box2, h2, box1, sumObject, lock));
    struct thread *thread1 = thread_start_joinable(contribute, session1);
    
    struct session *session2 = malloc(sizeof(struct session));
    if (session2 == 0) {
        abort();
    }
    session2->sum_object = sumObject;
    session2->lock = lock;
    //@ close contribute_pre(session2, box1, h1, box2, h2, box2, sumObject, lock);
    //@ close thread_run_pre(contribute)(session2, contribute_info(box1, h1, box2, h2, box2, sumObject, lock));
    struct thread *thread2 = thread_start_joinable(contribute, session2);
    
    thread_join(thread1);
    //@ open thread_run_post(contribute)(session1, _);
    
    thread_join(thread2);
    //@ open thread_run_post(contribute)(session2, _);
    
    //@ merge_fractions lock(lock, _, _);
    lock_dispose(lock);
    
    //@ open sum(sumObject, box1, h1, box2, h2)();
    
    int sum = sumObject->sum;
    assert(sum == 2);
    free(sumObject);

    //@ dispose_box contrib_box(box1, _, _);
    //@ open contrib_handle(h1, box1; _);
    //@ dispose_box contrib_box(box2, _, _);
    //@ open contrib_handle(h2, box2; _);

    return 0;
}