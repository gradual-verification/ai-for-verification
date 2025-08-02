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
    [1/2]d->phase1 |-> writing_x &*& [1/2]d->inside1 |-> false &*& [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x1 |-> ?_ &*& d->i |-> ?_ &*&
    [1/3]d->barrier |-> ?barrier &*& [1/2]barrier(barrier, 2, my_barrier_inv(d));

predicate_family_instance thread_run_post(thread1)(struct data *d, any info) =
    [1/2]d->phase1 |-> writing_x &*& [1/2]d->inside1 |-> false &*& [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x1 |-> ?_ &*& d->i |-> 0 &*&
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
        /*@
        invariant
            mutex_held(mutex, barrier_inv(barrier, n, inv), currentThread, f) &*&
            barrier_inv(barrier, n, inv)() &*&
            barrier_incoming(enter)(n, inv, exit) &*& is_barrier_enter(enter) &*& is_barrier_exit(exit);
        @*/
        {
            mutex_release(mutex);
            mutex_acquire(mutex);
        }
    }

    barrier->k++;
    if (barrier->k == barrier->n) {
        barrier->outgoing = true;
        barrier->k--;
        
        //@ open barrier_inv(barrier, n, inv)();
        //@ open barrier_incoming(enter)(n, inv, exit);
        //@ enter(n - 1);
        //@ close barrier_inv(barrier, n, inv)();
        
        mutex_release(barrier->mutex);
    } else {
        while (!barrier->outgoing)
        /*@
        invariant
            mutex_held(mutex, barrier_inv(barrier, n, inv), currentThread, f) &*&
            barrier_inv(barrier, n, inv)() &*&
            barrier_incoming(enter)(n, inv, exit) &*& is_barrier_enter(enter) &*& is_barrier_exit(exit);
        @*/
        {
            mutex_release(mutex);
            mutex_acquire(mutex);
        }

        barrier->k--;
        if (barrier->k == 0) {
            barrier->outgoing = false;
        }
        
        //@ open barrier_inv(barrier, n, inv)();
        //@ open barrier_incoming(enter)(n, inv, exit);
        //@ enter(barrier->k);
        //@ if (barrier->k == n - 1) { } else { exit(barrier->k + 1); }
        //@ close barrier_inv(barrier, n, inv)();
        
        mutex_release(mutex);
    }
}


// TODO: make this function pass the verification
void thread1(struct data *d) //@ : thread_run_joinable
    //@ requires thread_run_pre(thread1)(d, ?info);
    //@ ensures thread_run_post(thread1)(d, info);
{
    //@ open thread_run_pre(thread1)(d, ?info_);
    struct barrier *barrier = d->barrier;
    
    /*@
    predicate_family_instance barrier_incoming(enter)(int n, predicate(int k, bool outgoing) inv, barrier_exit *exit) =
        n == 2 &*& inv == my_barrier_inv(d) &*& exit == exit_ &*&
        [1/2]d->inside1 |-> false &*& [1/2]d->phase1 |-> writing_x &*&
        [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x1 |-> ?_ &*& d->i |-> ?_;
    
    predicate_family_instance barrier_inside(exit_)(int n, predicate(int k, bool outgoing) inv) =
        n == 2 &*& inv == my_barrier_inv(d) &*&
        [1/2]d->inside1 |-> true &*& [1/2]d->phase1 |-> writing_x &*&
        [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x1 |-> ?_ &*& d->i |-> ?_;
    
    predicate_family_instance barrier_exiting(exit_)(int n, predicate(int k, bool outgoing) inv) =
        n == 2 &*& inv == my_barrier_inv(d) &*&
        [1/2]d->inside1 |-> true &*& [1/2]d->phase1 |-> writing_x &*&
        [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x1 |-> ?_ &*& d->i |-> ?_;
    
    lemma void enter(int k) : barrier_enter
        requires barrier_incoming(enter)(?n, ?inv, ?exit) &*& inv(k, false) &*& 0 <= k &*& k < n;
        ensures
            k == n - 1 ?
                barrier_exiting(exit)(n, inv) &*& inv(k, true)
            :
                barrier_inside(exit)(n, inv) &*& inv(k + 1, false);
    {
        open barrier_incoming(enter)(n, inv, exit);
        d->inside1 = true;
        if (k == n - 1) {
            close barrier_exiting(exit_)(n, inv);
            close inv(k, true);
        } else {
            close barrier_inside(exit_)(n, inv);
            close inv(k + 1, false);
        }
    }
    
    lemma void exit_(int k) : barrier_exit
        requires barrier_inside(exit_)(?n, ?inv) &*& inv(k, true) &*& 1 <= k &*& k < n;
        ensures barrier_exiting(exit_)(n, inv) &*& k == 1 ? inv(0, false) : inv(k - 1, true);
    {
        open barrier_inside(exit_)(n, inv);
        close barrier_exiting(exit_)(n, inv);
        if (k == 1) {
            close inv(0, false);
        } else {
            close inv(k - 1, true);
        }
    }
    @*/
    
    //@ close barrier_incoming(enter)(2, my_barrier_inv(d), exit_);
    //@ produce_lemma_function_pointer_chunk(enter);
    //@ produce_lemma_function_pointer_chunk(exit_);
    barrier(barrier);
    //@ open barrier_exiting(exit_)(2, my_barrier_inv(d));

    int N = 0;
    while (N < 30)
    /*@
    invariant
        0 <= N &*& N <= 30 &*&
        [1/2]d->inside1 |-> true &*& [1/2]d->phase1 |-> writing_x &*&
        [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x1 |-> ?_ &*& d->i |-> ?_ &*&
        [1/3]d->barrier |-> barrier &*& [1/2]barrier(barrier, 2, my_barrier_inv(d));
    @*/
    {
        int a1 = d->x1;
        int a2 = d->x2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->y1 = a1 + 2 * a2;
        
        /*@
        predicate_family_instance barrier_incoming(enter2)(int n, predicate(int k, bool outgoing) inv, barrier_exit *exit) =
            n == 2 &*& inv == my_barrier_inv(d) &*& exit == exit2_ &*&
            [1/2]d->inside1 |-> true &*& [1/2]d->phase1 |-> writing_x &*&
            [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x1 |-> ?_;
        
        predicate_family_instance barrier_inside(exit2_)(int n, predicate(int k, bool outgoing) inv) =
            n == 2 &*& inv == my_barrier_inv(d) &*&
            [1/2]d->inside1 |-> true &*& [1/2]d->phase1 |-> writing_y &*&
            [1/2]d->x1 |-> ?_ &*& [1/2]d->x2 |-> ?_ &*& d->y1 |-> ?_;
        
        predicate_family_instance barrier_exiting(exit2_)(int n, predicate(int k, bool outgoing) inv) =
            n == 2 &*& inv == my_barrier_inv(d) &*&
            [1/2]d->inside1 |-> true &*& [1/2]d->phase1 |-> writing_y &*&
            [1/2]d->x1 |-> ?_ &*& [1/2]d->x2 |-> ?_ &*& d->y1 |-> ?_;
        
        lemma void enter2(int k) : barrier_enter
            requires barrier_incoming(enter2)(?n, ?inv, ?exit) &*& inv(k, false) &*& 0 <= k &*& k < n;
            ensures
                k == n - 1 ?
                    barrier_exiting(exit)(n, inv) &*& inv(k, true)
                :
                    barrier_inside(exit)(n, inv) &*& inv(k + 1, false);
        {
            open barrier_incoming(enter2)(n, inv, exit);
            d->phase1 = writing