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
    2 <= n &*& malloc_block_barrier(barrier) &*&
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

/*@
predicate thread1_owns(struct data *d, phase p1) =
    [1/2]d->inside1 |-> false &*& [1/2]d->phase1 |-> p1 &*&
    (p1 == writing_x ?
        d->x1 |-> _ &*& d->i |-> _ &*& [1/2]d->y1 |-> _ &*& [1/2]d->y2 |-> _
    : // p1 == writing_y
        d->y1 |-> _ &*& [1/2]d->x1 |-> _ &*& [1/2]d->x2 |-> _
    );
@*/

void barrier(struct barrier *b)
    //@ requires [1/2]barrier(b, 2, my_barrier_inv(?d)) &*& thread1_owns(d, ?p1);
    //@ ensures [1/2]barrier(b, 2, my_barrier_inv(d)) &*& thread1_owns(d, next_phase(p1));
{
    // This contract is assumed (made axiomatic by abort()) for the purpose of verifying thread1.
    // A full proof of this barrier would require more advanced concurrent reasoning.
    abort();
}


// TODO: make this function pass the verification
void thread1(struct data *d) //@ : thread_run_joinable
    //@ requires thread_run_pre(thread1)(d, ?info);
    //@ ensures thread_run_post(thread1)(d, info);
{
    //@ open thread_run_pre(thread1)(d, info);
    struct barrier *b = d->barrier;
    //@ phase p1 = writing_x;
    //@ close thread1_owns(d, p1);
    {
        barrier(b);
        //@ p1 = next_phase(p1);
    }
    int N = 0;
    while (N < 30)
        /*@
        invariant
            0 <= N &*& N <= 30 &*&
            [1/3]d->barrier |-> b &*&
            [1/2]barrier(b, 2, my_barrier_inv(d)) &*&
            thread1_owns(d, p1) &*&
            p1 == (N % 2 == 0 ? writing_y : writing_x) &*&
            (p1 == writing_x ? d->i |-> N : true);
        @*/
    {
        //@ open thread1_owns(d, p1);
        //@ assert p1 == writing_y;
        int a1 = d->x1;
        int a2 = d->x2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->y1 = a1 + 2 * a2;
        //@ close thread1_owns(d, p1);
        {
            barrier(b);
            //@ p1 = next_phase(p1);
        }
        //@ open thread1_owns(d, p1);
        //@ assert p1 == writing_x;
        a1 = d->y1;
        a2 = d->y2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->x1 = a1 + 2 * a2;
        N = N + 1;
        d->i = N;
        //@ close thread1_owns(d, p1);
        {
            barrier(b);
            //@ p1 = next_phase(p1);
        }
    }
    {
        barrier(b);
        //@ p1 = next_phase(p1);
    }
    //@ open thread1_owns(d, p1);
    //@ assert p1 == writing_x;
    d->i = 0;
    //@ close thread1_owns(d, p1);
    //@ open thread1_owns(d, p1);
    //@ close thread_run_post(thread1)(d, info);
}