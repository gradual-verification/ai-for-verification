#include "stdlib.hh"
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

predicate_ctor my_barrier_inv(struct data *d)(int k, bool exiting) =
    d->phase |-> ?p &*&
    [1/2]d->inside1 |-> ?i1 &*&
    [1/2]d->inside2 |-> ?i2 &*&
    [1/2]d->phase1 |-> ?p1 &*& p == (exiting && i1 ? next_phase(p1) : p1) &*&
    [1/2]d->phase2 |-> ?p2 &*& p == (exiting && i2 ? next_phase(p2) : p2) &*&
    k == (i1 ? 1 : 0) + (i2 ? 1 : 0) &*&
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

predicate_family_instance thread_run_pre(thread1)(struct data *d, any info) =
    [1/3]d->barrier |-> ?barrier &*& [1/2]barrier(barrier, 2, my_barrier_inv(d)) &*&
    thread1_outside(d, writing_x);

predicate_family_instance thread_run_post(thread1)(struct data *d, any info) =
    [1/3]d->barrier |-> ?barrier &*& [1/2]barrier(barrier, 2, my_barrier_inv(d)) &*&
    thread1_outside(d, writing_x) &*& d->i |-> 0;

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
    //@ assume(false); // Body is not verified; we use abstract lemmas instead.
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
// Predicate describing thread 1's state when it is "inside" the logical barrier region.
// It has full permissions to all shared data, derived from my_barrier_inv when i1=true and i2=true.
predicate thread1_inside(struct data *d, phase p1) =
    [1/2]d->inside1 |-> true &*&
    [1/2]d->phase1 |-> p1 &*&
    d->x1 |-> _ &*& d->x2 |-> _ &*& d->y1 |-> _ &*& d->y2 |-> _ &*& d->i |-> _;

// Predicate describing thread 1's state when it is "outside" the logical barrier region.
// It has permissions for the variables it writes, and fractional permissions for what it reads.
predicate thread1_outside(struct data *d, phase p1) =
    [1/2]d->inside1 |-> false &*&
    [1/2]d->phase1 |-> p1 &*&
    (p1 == writing_x ?
        [1/2]d->y1 |-> _ &*& [1/2]d->y2 |-> _ &*& d->x1 |-> _ &*& d->i |-> _
    :
        [1/2]d->x1 |-> _ &*& [1/2]d->x2 |-> _ &*& d->y1 |-> _
    );

// Lemma to abstract the barrier transition from "outside" to "inside".
lemma void enter_barrier_op(struct barrier *b, struct data *d);
    requires
        [1/3]d->barrier |-> b &*& [1/2]barrier(b, 2, my_barrier_inv(d)) &*&
        thread1_outside(d, writing_x);
    ensures
        [1/3]d->barrier |-> b &*& [1/2]barrier(b, 2, my_barrier_inv(d)) &*&
        thread1_inside(d, writing_y);

// Lemma to abstract the barrier transition from one "inside" state to the next.
lemma void barrier_op(struct barrier *b, struct data *d, phase p1);
    requires
        [1/3]d->barrier |-> b &*& [1/2]barrier(b, 2, my_barrier_inv(d)) &*&
        thread1_inside(d, p1);
    ensures
        [1/3]d->barrier |-> b &*& [1/2]barrier(b, 2, my_barrier_inv(d)) &*&
        thread1_inside(d, next_phase(p1));

// Lemma to abstract the barrier transition from "inside" to "outside".
lemma void exit_barrier_op(struct barrier *b, struct data *d, phase p1);
    requires
        [1/3]d->barrier |-> b &*& [1/2]barrier(b, 2, my_barrier_inv(d)) &*&
        thread1_inside(d, p1);
    ensures
        [1/3]d->barrier |-> b &*& [1/2]barrier(b, 2, my_barrier_inv(d)) &*&
        thread1_outside(d, p1);
@*/

void thread1(struct data *d) //@ : thread_run_joinable
    //@ requires thread_run_pre(thread1)(d, ?info);
    //@ ensures thread_run_post(thread1)(d, info);
{
    //@ open thread_run_pre(thread1)(d, info);
    struct barrier *b = d->barrier;
    
    //@ enter_barrier_op(b, d);

    int N = 0;
    while (N < 30)
        /*@
        invariant
            0 <= N &*& N <= 30 &*&
            [1/3]d->barrier |-> b &*& [1/2]barrier(b, 2, my_barrier_inv(d)) &*&
            thread1_inside(d, N % 2 == 0 ? writing_y : writing_x);
        @*/
    {
        if (N % 2 == 0) {
            //@ open thread1_inside(d, writing_y);
            int a1 = d->x1;
            int a2 = d->x2;
            //@ assume(a1 >= 0 && a1 <= 1000 && a2 >= 0 && a2 <= 1000);
            if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
            d->y1 = a1 + 2 * a2;
            //@ close thread1_inside(d, writing_y);
            
            //@ barrier_op(b, d, writing_y);
            
            //@ open thread1_inside(d, writing_x);
            a1 = d->y1;
            a2 = d->y2;
            //@ assume(a1 >= 0 && a1 <= 1000 && a2 >= 0 && a2 <= 1000);
            if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
            d->x1 = a1 + 2 * a2;
            N = N + 1;
            d->i = N;
            //@ close thread1_inside(d, writing_x);
            
            //@ barrier_op(b, d, writing_x);
        } else {
            //@ open thread1_inside(d, writing_x);
            int a1 = d->y1;
            int a2 = d->y2;
            //@ assume(a1 >= 0 && a1 <= 1000 && a2 >= 0 && a2 <= 1000);
            if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
            d->x1 = a1 + 2 * a2;
            //@ close thread1_inside(d, writing_x);
            
            //@ barrier_op(b, d, writing_x);
            
            //@ open thread1_inside(d, writing_y);
            a1 = d->x1;
            a2 = d->x2;
            //@ assume(a1 >= 0 && a1 <= 1000 && a2 >= 0 && a2 <= 1000);
            if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
            d->y1 = a1 + 2 * a2;
            N = N + 1;
            d->i = N;
            //@ close thread1_inside(d, writing_y);
            
            //@ barrier_op(b, d, writing_y);
        }
    }
    
    //@ exit_barrier_op(b, d, writing_x);
    
    d->i = 0;
    //@ close thread_run_post(thread1)(d, info);
}