        invariant l->readers |-> length(reader_handles);
#include "stdlib.h"
#include "threading.h"
//@ #include "listex.gh"

// A simple reader-writer lock implementation
struct rwlock {
    struct mutex *mutex;
    int readers;
    //@ box boxId;
};

/*@

box_class rwlock_box(struct rwlock *l, list<handle> reader_handles) {
    invariant l->readers |-> length(reader_handles);

    action enter_reader();
        requires true;
        ensures reader_handles == cons(actionHandle, old_reader_handles);

    action leave_reader();
        requires mem(actionHandle, old_reader_handles) == true;
        ensures reader_handles == remove(actionHandle, old_reader_handles);

    handle_predicate is_reader() {
        invariant mem(predicateHandle, reader_handles) == true;

        preserved_by enter_reader() {
            // The new handle `actionHandle` is different from existing `predicateHandle`s.
            // mem(predicateHandle, old_reader_handles) implies mem(predicateHandle, cons(actionHandle, old_reader_handles))
        }
        preserved_by leave_reader() {
            // This is checked for other handles, not the one being consumed.
            // Since actionHandle != predicateHandle, the invariant holds.
        }
    }
}

predicate_ctor rwlock_inv(struct rwlock *l, box boxId)() =
    rwlock_box(boxId, l, _);

@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `reader` function acquires shared access by using the reader-writer lock. 
 * It first increments the number of readers, and then decrements it after the critical section (using mutex).
 *
 * @param l: the reader-writer lock to be used, which has the mutex and has number of readers >= 0
 * 
 */
void reader(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(reader)(l);
    //@ ensures lockset(currentThread, nil);
{
    //@ open thread_run_data(reader)(l);
    //@ handle h;
    mutex_acquire(l->mutex);
    //@ open rwlock_inv(l, l->boxId)();

    //@ h = create_handle rwlock_box_handle(l->boxId);
    /*@
    consuming_box_predicate rwlock_box(l->boxId, l, ?handles)
    consuming_handle_predicate rwlock_box_handle(h)
    perform_action enter_reader() {
    @*/
        if (l->readers == INT_MAX) {
            abort();
        }
        l->readers++;
        //@ length_cons(h, handles);
    /*@
    }
    producing_box_predicate rwlock_box(l, cons(h, handles))
    producing_handle_predicate is_reader();
    @*/

    //@ close rwlock_inv(l, l->boxId)();
    mutex_release(l->mutex);

    // critical section (reading)

    mutex_acquire(l->mutex);
    //@ open rwlock_inv(l, l->boxId)();

    /*@
    consuming_box_predicate rwlock_box(l->boxId, l, ?handles_new)
    consuming_handle_predicate is_reader(h)
    perform_action leave_reader() {
    @*/
        //@ open is_reader(h, l->boxId, _);
        //@ assert mem(h, handles_new) == true;
        //@ mem_length(h, handles_new);
        if (l->readers == 0) {
            abort();
        }
        l->readers--;
        //@ length_remove(h, handles_new);
    /*@
    }
    producing_box_predicate rwlock_box(l, remove(h, handles_new))
    producing_handle_predicate rwlock_box_handle();
    @*/
    //@ leak rwlock_box_handle(h, l->boxId);

    //@ close rwlock_inv(l, l->boxId)();
    mutex_release(l->mutex);
    
    //@ leak [_]l->mutex |-> _ &*& [_]l->boxId |-> _ &*& [_]mutex(_, _);
}

/*@
// We define the thread_run_data predicate family to set up the initial state for a reader thread.
// Each reader thread gets a dummy fraction of the lock's data and a fractional permission to the mutex.
// This allows multiple reader threads to coexist and use the lock.
predicate_family_instance thread_run_data(reader)(void *data) =
    let l = (struct rwlock *)data;
    [_]l->mutex |-> ?m &*&
    [_]l->boxId |-> ?boxId &*&
    [_]mutex(m, rwlock_inv(l, boxId));
@*/