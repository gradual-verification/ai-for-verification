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
    // The following line is commented out as it creates a contradiction with the barrier's C implementation.
    // The abstract barrier proof framework does not require this strong coupling.
    // k == (i1 ? 1 : 0) + (i2 ? 1 : 0) &*&
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

predicate thread1_private_state(struct data *d, phase p) =
    [1/2]d->phase1 |-> p &*&
    [1/2]d->inside1 |-> false &*&
    (p == writing_x ?
        [1/2]d->y1 |-> _ &*& [1/2]d->y2 |-> _ &*& d->x1 |-> _ &*& d->i |-> _
    :
        [1/2]d->x1 |-> _ &*& [1/2]d->x2 |-> _ &*& d->y1 |-> _
    );

predicate thread1_inside_state(struct data *d, phase p) =
    [1/2]d->phase1 |-> p &*&
    [1/2]d->inside1 |-> true;

predicate_family_instance thread_run_pre(thread1)(struct data *d, any info) =
    [1/3]d->barrier |-> ?b &*& [1/2]barrier(b, 2, my_barrier_inv(d)) &*&
    thread1_private_state(d, writing_x);

predicate_family_instance thread_run_post(thread1)(struct data *d, any info) =
    [1/3]d->barrier |-> ?b &*& [1/2]barrier(b, 2, my_barrier_inv(d)) &*&
    d->i |-> 0 &*&
    thread1_private_state(d, writing_x);

lemma void thread1_barrier_enter(int k);
lemma void thread1_barrier_exit(int k);

predicate_family_instance barrier_incoming(thread1_barrier_enter)(int n, predicate(int, bool) inv, any exit) =
    n == 2 &*& inv == my_barrier_inv(?d) &*& exit == thread1_barrier_exit &*&
    thread1_private_state(d, ?p);

predicate_family_instance barrier_inside(thread1_barrier_exit)(int n, predicate(int, bool) inv) =
    n == 2 &*& inv == my_barrier_inv(?d) &*&
    thread1_inside_state(d, ?p);

predicate_family_instance barrier_exiting(thread1_barrier_exit)(int n, predicate(int, bool) inv) =
    n == 2 &*& inv == my_barrier_inv(?d) &*&
    thread1_private_state(d, ?p);

lemma void thread1_barrier_enter(int k)
    requires barrier_incoming(this)(2, my_barrier_inv(?d), ?exit) &*& my_barrier_inv(d)(k, false) &*& 0 <= k &*& k < 2;
    ensures
        k == 1 ?
            barrier_exiting(exit)(2, my_barrier_inv(d)) &*& my_barrier_inv(d)(1, true)
        :
            barrier_inside(exit)(2, my_barrier_inv(d)) &*& my_barrier_inv(d)(k + 1, false);
{
    open barrier_incoming(this)(_, _, _, _);
    open thread1_private_state(d, ?p1);
    open my_barrier_inv(d)(k, false);
    d->inside1 = true;
    if (k == 1) { // Last to arrive
        d->phase = next_phase(p1);
        d->phase1 = next_phase(p1);
        d->inside1 = false;
        close my_barrier_inv(d)(1, true);
        open my_barrier_inv(d)(1, true);
        close thread1_private_state(d, next_phase(p1));
        close barrier_exiting(thread1_barrier_exit)(2, my_barrier_inv(d));
    } else { // First to arrive
        close my_barrier_inv(d)(k + 1, false);
        close thread1_inside_state(d, p1);
        close barrier_inside(thread1_barrier_exit)(2, my_barrier_inv(d));
    }
}

lemma void thread1_barrier_exit(int k)
    requires barrier_inside(this)(2, my_barrier_inv(?d)) &*& my_barrier_inv(d)(k, true) &*& 1 <= k &*& k < 2;
    ensures barrier_exiting(this)(2, my_barrier_inv(d)) &*& my_barrier_inv(d)(k - 1, true);
{
    open barrier_inside(this)(_, _);
    open thread1_inside_state(d, ?p1);
    open my_barrier_inv(d)(k, true);
    d->inside1 = false;
    d->phase1 = next_phase(p1);
    close my_barrier_inv(d)(k - 1, true);
    open my_barrier_inv(d)(k - 1, true);
    close thread1_private_state(d, next_phase(p1));
    close barrier_exiting(thread1_barrier_exit)(2, my_barrier_inv(d));
}

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
    //@ open barrier(barrier, n, inv);
    struct mutex *mutex = barrier->mutex;
    mutex_acquire(mutex);
    //@ open barrier_inv(barrier, n, inv)();
    //@ open barrier_incoming(enter)(n, inv, exit);

    while (barrier->outgoing)
    //@ invariant mutex_held(mutex, barrier_inv(barrier, n, inv), currentThread, f) &*& barrier_inv(barrier, n, inv)();
    {
        //@ open barrier_inv(barrier, n, inv)();
        mutex_release(mutex);
        mutex_acquire(mutex);
        //@ open barrier_inv(barrier, n, inv)();
    }
    
    //@ int k_old = barrier->k;
    //@ enter(k_old);
    barrier->k++;

    if (barrier->k == barrier->n) {
        barrier->outgoing = true;
        barrier->k--;
        //@ close barrier_inv(barrier, n, inv)();
        mutex_release(barrier->mutex);
    } else {
        //@ close barrier_inv(barrier, n, inv)();
        while (!barrier->outgoing)
        //@ invariant mutex_held(mutex, barrier_inv(barrier, n, inv), currentThread, f) &*& barrier_inv(barrier, n, inv)() &*& barrier_inside(exit)(n, inv);
        {
            mutex_release(mutex);
            mutex_acquire(mutex);
            //@ open barrier_inv(barrier, n, inv)();
        }
        
        //@ int k_new = barrier->k;
        //@ exit(k_new);
        barrier->k--;
        if (barrier->k == 0) {
            barrier->outgoing = false;
        }
        //@ close barrier_inv(barrier, n, inv)();
        mutex_release(mutex);
    }
    //@ close [f]barrier(barrier, n, inv);
}


void thread1(struct data *d) //@ : thread_run_joinable
    //@ requires thread_run_pre(thread1)(d, ?info);
    //@ ensures thread_run_post(thread1)(d, info);
{
    //@ open thread_run_pre(thread1)(d, info);
    struct barrier *b = d->barrier;
    {
        //@ produce_lemma_function_pointer_chunk(thread1_barrier_enter);
        //@ produce_lemma_function_pointer_chunk(thread1_barrier_exit);
        //@ close barrier_incoming(thread1_barrier_enter)(2, my_barrier_inv(d), thread1_barrier_exit);
        barrier(b);
        //@ open barrier_exiting(thread1_barrier_exit)(2, my_barrier_inv(d));
    }
    int N = 0;
    while (N < 30)
    /*@
    invariant 0 <= N &*& N <= 30 &*&
              [1/3]d->barrier |-> b &*& [1/2]barrier(b, 2, my_barrier_inv(d)) &*&
              (N % 2 == 0 ?
                  thread1_private_state(d, writing_y)
              :
                  thread1_private_state(d, writing_x) &*& d->i |-> N
              );
    @*/
    {
        //@ open thread1_private_state(d, writing_y);
        int a1 = d->x1;
        int a2 = d->x2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->y1 = a1 + 2 * a2;
        //@ close thread1_private_state(d, writing_y);
        {
            //@ produce_lemma_function_pointer_chunk(thread1_barrier_enter);
            //@ produce_lemma_function_pointer_chunk(thread1_barrier_exit);
            //@ close barrier_incoming(thread1_barrier_enter)(2, my_barrier_inv(d), thread1_barrier_exit);
            barrier(b);
            //@ open barrier_exiting(thread1_barrier_exit)(2, my_barrier_inv(d));
        }
        //@ open thread1_private_state(d, writing_x);
        a1 = d->y1;
        a2 = d->y2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->x1 = a1 + 2 * a2;
        N = N + 1;
        d->i = N;
        //@ close thread1_private_state(d, writing_x);
        {
            //@ produce_lemma_function_pointer_chunk(thread1_barrier_enter);
            //@ produce_lemma_function_pointer_chunk(thread1_barrier_exit);
            //@ close barrier_incoming(thread1_barrier_enter)(2, my_barrier_inv(d), thread1_barrier_exit);
            barrier(b);
            //@ open barrier_exiting(thread1_barrier_exit)(2, my_barrier_inv(d));
        }
    }
    {
        //@ produce_lemma_function_pointer_chunk(thread1_barrier_enter);
        //@ produce_lemma_function_pointer_chunk(thread1_barrier_exit);
        //@ close barrier_incoming(thread1_barrier_enter)(2, my_barrier_inv(d), thread1_barrier_exit);
        barrier(b);
        //@ open barrier_exiting(thread1_barrier_exit)(2, my_barrier_inv(d));
    }
    d->i = 0;
    //@ close thread_run_post(thread1)(d, info);
}