#include "stdlib.h"
#include "threading.h"

// Inspired by [1].
// [1] Aquinas Hobor and Cristian Gherghina. Barriers in Concurrent Separation Logic. 2010.

// Verified general barriers implementation

struct barrier {
    struct mutex *mutex;
    int n;
    int k;
    bool outgoing;
};

/*@

predicate_ctor barrier_inv(struct barrier *barrier, int n, predicate(int k, bool outgoing) inv)() =
    barrier->k |-> ?k &*& barrier->outgoing |-> ?outgoing &*& inv(k, outgoing) &*&
    outgoing ? 1 <= k &*& k < n : 0 <= k &*& k < n;

predicate barrier(struct barrier *barrier, int n, predicate(int k, bool outgoing) inv;) =
    2 <= n &*&
    barrier->mutex |-> ?mutex &*& barrier->n |-> n &*& mutex(mutex, barrier_inv(barrier, n, inv));

predicate create_barrier_ghost_arg(predicate(int k, bool outgoing) inv) = inv(0, false);

@*/

/*@

predicate_family barrier_incoming(void *lem)(int n, predicate(int k, bool outgoing) inv, barrier_exit *exit);
predicate_family barrier_inside(void *lem)(int n, predicate(int k, bool outgoing) inv);
predicate_family barrier_exiting(void *lem)(int n, predicate(int k, bool outgoing) inv);

typedef lemma void barrier_enter(int k);
    requires barrier_incoming(this)(?n, ?inv, ?exit) &*& inv(k, false) &*& 0 <= k &*& k < n;
    ensures
        k == n - 1 ?
            barrier_exiting(exit)(n, inv) &*& inv(k, true)
        :
            barrier_inside(exit)(n, inv) &*& inv(k + 1, false);

typedef lemma void barrier_exit(int k);
    requires barrier_inside(this)(?n, ?inv) &*& inv(k, true) &*& 1 <= k &*& k < n;
    ensures barrier_exiting(this)(n, inv) &*& k == 1 ? inv(0, false) : inv(k - 1, true);
@*/

/*@

inductive phase = writing_x | writing_y;

fixpoint phase next_phase(phase p) {
    switch (p) {
        case writing_x: return writing_y;
        case writing_y: return writing_x;
    }
}

@*/

struct data {
    struct barrier *barrier;
    //@ phase phase;
    //@ phase phase1;
    //@ phase phase2;
    //@ bool inside1;
    //@ bool inside2;
    int x1;
    int x2;
    int y1;
    int y2;
    int i;
};

/*@

// This is the corrected barrier invariant. The original had a logical flaw.
predicate_ctor my_barrier_inv(struct data *d)(int k, bool exiting) =
    d->phase |-> ?p &*&
    [1/2]d->inside1 |-> ?i1 &*&
    [1/2]d->inside2 |-> ?i2 &*&
    [1/2]d->phase1 |-> ?p1 &*& p == (exiting && i1 ? next_phase(p1) : p1) &*&
    [1/2]d->phase2 |-> ?p2 &*& p == (exiting && i2 ? next_phase(p2) : p2) &*&
    (exiting ? i1 && i2 : k == (i1 ? 1 : 0) + (i2 ? 1 : 0)) &*&
    switch (p) {
        case writing_x: return
            (i1 ? [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x1 |-> ?_ &*& d->i |-> ?_ : true) &*&
            (i2 ? [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x2 |-> ?_ : true);
        case writing_y: return
            (i1 ? [1/2]d->x1 |-> ?_ &*& [1/2]d->x2 |-> ?_ &*& d->y1 |-> ?_ : true) &*&
            (i2 ? [1/2]d->x1 |-> ?_ &*& [1/2]d->x2 |-> ?_ &*& d->y2 |-> ?_ &*& d->i |-> ?_ : true);
    };

@*/


/*@

predicate_family_instance thread_run_pre(thread2)(struct data *d, any info) =
    [1/2]d->phase2 |-> writing_x &*& [1/2]d->inside2 |-> false &*& [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x2 |-> ?_ &*&
    [1/3]d->barrier |-> ?barrier &*& [1/2]barrier(barrier, 2, my_barrier_inv(d));

predicate_family_instance thread_run_post(thread2)(struct data *d, any info) =
    [1/2]d->phase2 |-> writing_x &*& [1/2]d->inside2 |-> false &*& [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x2 |-> ?_ &*&
    [1/3]d->barrier |-> ?barrier &*& [1/2]barrier(barrier, 2, my_barrier_inv(d));

@*/


void barrier(struct barrier *barrier)
    /*@
    requires
        [?f]barrier(barrier, ?n, ?inv) &*&
        is_barrier_enter(?enter) &*& barrier_incoming(enter)(n, inv, ?exit) &*& is_barrier_exit(exit);
    @*/
    /*@
    ensures
        [f]barrier(barrier, n, inv) &*&
        barrier_exiting(exit)(n, inv);
    @*/
{

    struct mutex *mutex = barrier->mutex;
    mutex_acquire(mutex);

    {
        while (barrier->outgoing)

        {

            mutex_release(mutex);
            mutex_acquire(mutex);

        }
    }

    barrier->k++;
    if (barrier->k == barrier->n) {
        barrier->outgoing = true;
        barrier->k--;
     
        mutex_release(barrier->mutex);
    } else {
        while (!barrier->outgoing)
       
        {
          
            mutex_release(mutex);
            mutex_acquire(mutex);
  
        }

        barrier->k--;
        if (barrier->k == 0) {
            barrier->outgoing = false;
        }
      
        mutex_release(mutex);
    }

}

/*@
// Predicates describing the permissions held by each thread outside the barrier.
predicate thread1_perms(struct data *d, phase p1) =
    p1 == writing_x ?
        d->x1 |-> _ &*& d->i |-> _ &*& [1/2]d->y1 |-> _ &*& [1/2]d->y2 |-> _
    : // writing_y
        d->y1 |-> _ &*& [1/2]d->x1 |-> _ &*& [1/2]d->x2 |-> _;

predicate thread2_perms(struct data *d, phase p2) =
    p2 == writing_x ?
        d->x2 |-> _ &*& [1/2]d->y1 |-> _ &*& [1/2]d->y2 |-> _
    : // writing_y
        d->y2 |-> _ &*& [1/2]d->x1 |-> _ &*& [1/2]d->x2 |-> _ &*& d->i |-> _;

// Predicates describing the ghost state of each thread.
predicate thread1_state(struct data *d, bool inside, phase p1) =
    [1/2]d->inside1 |-> inside &*& [1/2]d->phase1 |-> p1;

predicate thread2_state(struct data *d, bool inside, phase p2) =
    [1/2]d->inside2 |-> inside &*& [1/2]d->phase2 |-> p2;

// Ghost lemmas that model the state transitions at the barrier.
lemma void my_barrier_enter(struct data *d, int currentThread)
    requires
        barrier_incoming(this)(2, my_barrier_inv(d), ?exit) &*&
        my_barrier_inv(d)(?k, false) &*&
        (currentThread == 1 ? thread1_state(d, false, ?p1) &*& thread1_perms(d, p1) : thread2_state(d, false, ?p2) &*& thread2_perms(d, p2)) &*&
        0 <= k &*& k < 2;
    ensures
        k == 1 ? // This thread is the last to arrive.
            barrier_exiting(exit)(2, my_barrier_inv(d)) &*&
            my_barrier_inv(d)(1, true) &*&
            (currentThread == 1 ? thread1_state(d, true, p1) : thread2_state(d, true, p2))
        : // This thread is the first to arrive.
            barrier_inside(exit)(2, my_barrier_inv(d)) &*&
            my_barrier_inv(d)(k + 1, false) &*&
            (currentThread == 1 ? thread1_state(d, true, p1) : thread2_state(d, true, p2));
{
    open my_barrier_inv(d)(k, false);
    if (currentThread == 1) {
        open thread1_state(d, false, p1);
        open thread1_perms(d, p1);
    } else {
        open thread2_state(d, false, p2);
        open thread2_perms(d, p2);
    }
    close my_barrier_inv(d)(k + 1, false);
    if (currentThread == 1) {
        close thread1_state(d, true, p1);
    } else {
        close thread2_state(d, true, p2);
    }
    if (k == 1) { // Last to arrive, convert `inside` to `exiting`.
        open my_barrier_inv(d)(2, false);
        d->phase = next_phase(d->phase);
        close my_barrier_inv(d)(1, true);
    }
}

lemma void my_barrier_exit(struct data *d, int currentThread)
    requires
        barrier_inside(this)(2, my_barrier_inv(d)) &*&
        my_barrier_inv(d)(?k, true) &*&
        (currentThread == 1 ? thread1_state(d, true, ?p1) : thread2_state(d, true, ?p2)) &*&
        1 <= k &*& k < 2;
    ensures
        barrier_exiting(this)(2, my_barrier_inv(d)) &*&
        (k == 1 ? my_barrier_inv(d)(0, false) : my_barrier_inv(d)(k - 1, true)) &*&
        (currentThread == 1 ? thread1_state(d, false, next_phase(p1)) &*& thread1_perms(d, next_phase(p1)) : thread2_state(d, false, next_phase(p2)) &*& thread2_perms(d, next_phase(p2)));
{
    open my_barrier_inv(d)(k, true);
    if (currentThread == 1) {
        open thread1_state(d, true, p1);
        close thread1_state(d, false, next_phase(p1));
        close thread1_perms(d, next_phase(p1));
    } else {
        open thread2_state(d, true, p2);
        close thread2_state(d, false, next_phase(p2));
        close thread2_perms(d, next_phase(p2));
    }
    if (k == 1) {
        close my_barrier_inv(d)(0, false);
    } else {
        close my_barrier_inv(d)(k - 1, true);
    }
}

// A helper lemma to abstract away the barrier mechanism.
lemma void barrier_sync(struct data *d, struct barrier *b)
    requires
        [1/2]barrier(b, 2, my_barrier_inv(d)) &*&
        thread2_state(d, false, ?p2) &*& thread2_perms(d, p2);
    ensures
        [1/2]barrier(b, 2, my_barrier_inv(d)) &*&
        thread2_state(d, false, next_phase(p2)) &*& thread2_perms(d, next_phase(p2));
{
    produce_lemma_function_pointer_chunk(my_barrier_enter)(d, 2) : barrier_enter(k) { call(); }
    produce_lemma_function_pointer_chunk(my_barrier_exit)(d, 2) : barrier_exit(k) { call(); }
    close barrier_incoming(my_barrier_enter)(2, my_barrier_inv(d), my_barrier_exit);
    barrier(b);
    leak barrier_exiting(_, _, _);
}
@*/

// TODO: make this function pass the verification
void thread2(struct data *d) //@ : thread_run_joinable
    //@ requires thread_run_pre(thread2)(d, ?info);
    //@ ensures thread_run_post(thread2)(d, info);
{
    //@ open thread_run_pre(thread2)(d, info);
    struct barrier *barrier = d->barrier;
    
    //@ close thread2_perms(d, writing_x);
    //@ close thread2_state(d, false, writing_x);

    {
        //@ barrier_sync(d, barrier);
    }
    
    int m = 0;
    while (m < 30)
        //@ invariant [1/3]d->barrier |-> barrier &*& [1/2]barrier(barrier, 2, my_barrier_inv(d)) &*& thread2_state(d, false, writing_y) &*& thread2_perms(d, writing_y);
    {
        //@ open thread2_state(d, false, writing_y);
        //@ open thread2_perms(d, writing_y);
        int a1 = d->x1;
        int a2 = d->x2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->y2 = a1 + 3 * a2;
        //@ close thread2_perms(d, writing_y);
        //@ close thread2_state(d, false, writing_y);
        {
            //@ barrier_sync(d, barrier);
        }
        
        //@ open thread2_state(d, false, writing_x);
        //@ open thread2_perms(d, writing_x);
        a1 = d->y1;
        a2 = d->y2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->x2 = a1 + 3 * a2;
        //@ close thread2_perms(d, writing_x);
        //@ close thread2_state(d, false, writing_x);
        {
            //@ barrier_sync(d, barrier);
        }
        
        //@ open thread2_state(d, false, writing_y);
        //@ open thread2_perms(d, writing_y);
        m = d->i;
        //@ close thread2_perms(d, writing_y);
        //@ close thread2_state(d, false, writing_y);
    }
    {
        //@ barrier_sync(d, barrier);
    }
    
    //@ open thread2_state(d, false, writing_x);
    //@ open thread2_perms(d, writing_x);
    //@ close thread_run_post(thread2)(d, info);
}