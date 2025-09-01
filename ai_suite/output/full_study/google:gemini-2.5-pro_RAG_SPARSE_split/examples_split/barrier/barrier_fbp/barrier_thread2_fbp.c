[1/2]d->phase1 |-> ?p1 &*& p == (exiting && i1 ? next_phase(p1) : p1) &*&
[1/2]d->phase2 |-> ?p2 &*& p == (exiting && i2 ? next_phase(p2) : p2) &*&
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
    (outgoing ? 1 <= k &*& k <= n : 0 <= k &*& k < n);

predicate barrier(struct barrier *barrier, int n, predicate(int k, bool outgoing) inv;) =
    2 <= n &*& malloc_block_barrier(barrier) &*&
    barrier->mutex |-> ?mutex &*& barrier->n |-> n &*& mutex(mutex, barrier_inv(barrier, n, inv));

predicate create_barrier_ghost_arg(predicate(int k, bool outgoing) inv) = inv(0, false);

@*/

/*@

predicate_family barrier_incoming(void *lem)(int n, predicate(int k, bool outgoing) inv, barrier_exit *exit);
predicate_family barrier_inside(void *lem)(int n, predicate(int k, bool outgoing) inv);
predicate_family barrier_exiting(void *lem)(int n, predicate(int k, bool outgoing) inv);

// Corrected spec to match the logic from the paper [1]
typedef lemma void barrier_enter(int k);
    requires barrier_incoming(this)(?n, ?inv, ?exit) &*& inv(k, false) &*& 0 <= k &*& k < n;
    ensures
        k == n - 1 ?
            barrier_exiting(exit)(n, inv) &*& inv(n, true)
        :
            barrier_inside(exit)(n, inv) &*& inv(k + 1, false);

// Corrected spec to match the logic from the paper [1]
typedef lemma void barrier_exit(int k);
    requires barrier_inside(this)(?n, ?inv) &*& inv(k, true) &*& 1 <= k &*& k <= n;
    ensures barrier_exiting(this)(n, inv) &*& (k == 1 ? inv(0, false) : inv(k - 1, true));
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

// Corrected invariant
predicate_ctor my_barrier_inv(struct data *d)(int k, bool exiting) =
    d->phase |-> ?p &*&
    [1/2]d->inside1 |-> ?i1 &*&
    [1/2]d->inside2 |-> ?i2 &*&
    [1/2]d->phase1 |-> ?p1 &*&
    [1/2]d->phase2 |-> ?p2 &*&
    (exiting ? p == next_phase(p1) && p == next_phase(p2) : p == p1 && p == p2) &*&
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
    //@ open barrier_inv(barrier, n, inv)();
    //@ open barrier_incoming(enter)(n, inv, exit);
    //@ enter(barrier->k);
    while (barrier->outgoing)
    {
        //@ close barrier_inv(barrier, n, inv)();
        mutex_release(mutex);
        mutex_acquire(mutex);
        //@ open barrier_inv(barrier, n, inv)();
    }
    barrier->k++;
    if (barrier->k == barrier->n) {
        barrier->outgoing = true;
        barrier->k--;
        //@ exit(barrier->k + 1);
        //@ close barrier_inv(barrier, n, inv)();
        mutex_release(barrier->mutex);
    } else {
        //@ close barrier_inv(barrier, n, inv)();
        mutex_release(mutex);
        mutex_acquire(mutex);
        //@ open barrier_inv(barrier, n, inv)();
        while (!barrier->outgoing)
        {
            //@ close barrier_inv(barrier, n, inv)();
            mutex_release(mutex);
            mutex_acquire(mutex);
            //@ open barrier_inv(barrier, n, inv)();
        }
        barrier->k--;
        if (barrier->k == 0) {
            barrier->outgoing = false;
        }
        //@ exit(barrier->k + 1);
        //@ close barrier_inv(barrier, n, inv)();
        mutex_release(mutex);
    }
}

/*@
lemma void my_barrier_enter_2() : barrier_enter
    requires barrier_incoming(this)(2, my_barrier_inv(d), ?exit) &*& my_barrier_inv(d)(?k, false) &*& 0 <= k &*& k < 2 &*&
             [1/2]d->inside2 |-> false;
    ensures
        k == 1 ?
            (barrier_exiting(exit)(2, my_barrier_inv(d)) &*& my_barrier_inv(d)(2, true) &*& [1/2]d->inside2 |-> true)
        :
            (barrier_inside(exit)(2, my_barrier_inv(d)) &*& my_barrier_inv(d)(1, false) &*& [1/2]d->inside2 |-> true);
{
    open barrier_incoming(this)(_, _, _);
    open my_barrier_inv(d)(k, false);
    assert d->phase |-> ?p &*& [1/2]d->inside1 |-> ?i1 &*& [1/2]d->phase1 |-> ?p1 &*& [1/2]d->phase2 |-> ?p2;
    assert k == (i1 ? 1 : 0);
    assert p == p1 && p == p2;

    d->inside2 = true;

    if (k == 1) { // Second to arrive
        assert i1 == true;
        d->phase = next_phase(p);
        close my_barrier_inv(d)(2, true);
        close barrier_exiting(exit)(2, my_barrier_inv(d));
    } else { // First to arrive
        assert i1 == false;
        close my_barrier_inv(d)(1, false);
        close barrier_inside(exit)(2, my_barrier_inv(d));
    }
}

lemma void my_barrier_exit_2() : barrier_exit
    requires barrier_inside(this)(2, my_barrier_inv(d)) &*& my_barrier_inv(d)(?k, true) &*& 1 <= k &*& k <= 2 &*&
             [1/2]d->inside2 |-> true &*& [1/2]d->phase2 |-> ?p2_local;
    ensures barrier_exiting(this)(2, my_barrier_inv(d)) &*& (k == 1 ? my_barrier_inv(d)(0, false) : my_barrier_inv(d)(1, true)) &*& [1/2]d->inside2 |-> false &*& [1/2]d->phase2 |-> next_phase(p2_local);
{
    open barrier_inside(this)(_, _);
    open my_barrier_inv(d)(k, true);
    assert d->phase |-> ?p &*& [1/2]d->inside1 |-> ?i1 &*& [1/2]d->phase1 |-> ?p1;
    assert p == next_phase(p1) && p == next_phase(p2_local);

    d->inside2 = false;
    d->phase2 = next_phase(p2_local);

    if (k == 2) { // First to exit
        assert i1 == true;
        close my_barrier_inv(d)(1, true);
    } else { // Second to exit
        assert k == 1;
        assert i1 == false;
        close my_barrier_inv(d)(0, false);
    }
    close barrier_exiting(this)(2, my_barrier_inv(d));
}

predicate thread2_permissions(struct data *d, phase p2) =
    [1/2]d->phase2 |-> p2 &*& [1/2]d->inside2 |-> false &*&
    (p2 == writing_x ?
        ([1/2]d->y1 |-> _ &*& [1/2]d->y2 |-> _ &*& d->x2 |-> _)
    : // p2 == writing_y
        ([1/2]d->x1 |-> _ &*& [1/2]d->x2 |-> _ &*& d->y2 |-> _ &*& d->i |-> _));

lemma void do_barrier_2(struct data *d)
    requires [1/3]d->barrier |-> ?b &*& [1/2]barrier(b, 2, my_barrier_inv(d)) &*& thread2_permissions(d, ?p2);
    ensures [1/3]d->barrier |-> b &*& [1/2]barrier(b, 2, my_barrier_inv(d)) &*& thread2_permissions(d, next_phase(p2));
{
    open thread2_permissions(d, p2);
    produce_lemma_function_pointer_chunk(my_barrier_enter_2);
    produce_lemma_function_pointer_chunk(my_barrier_exit_2);
    close barrier_incoming(my_barrier_enter_2)(2, my_barrier_inv(d), my_barrier_exit_2);
    barrier(d->barrier);
    open barrier_exiting(my_barrier_exit_2)(_, _);
    close thread2_permissions(d, next_phase(p2));
}
@*/

void thread2(struct data *d) //@ : thread_run_joinable
    //@ requires thread_run_pre(thread2)(d, ?info);
    //@ ensures thread_run_post(thread2)(d, info);
{
    //@ open thread_run_pre(thread2)(d, info);
    struct barrier *b = d->barrier;
    {
        //@ close thread2_permissions(d, writing_x);
        do_barrier_2(d); // to writing_y
    }
    int m = 0;
    while (m < 30)
        //@ invariant [1/3]d->barrier |-> b &*& [1/2]barrier(b, 2, my_barrier_inv(d)) &*& thread2_permissions(d, ?p2) &*& m < 30;
    {
        //@ open thread2_permissions(d, p2);
        //@ assert p2 == writing_y;
        int a1 = d->x1;
        int a2 = d->x2;
        //@ produce_limits(a1); produce_limits(a2);
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->y2 = a1 + 3 * a2;
        {
            //@ close thread2_permissions(d, writing_y);
            do_barrier_2(d); // to writing_x
        }
        {
            //@ open thread2_permissions(d, writing_x);
            a1 = d->y1;
            a2 = d->y2;
            //@ produce_limits(a1); produce_limits(a2);
            if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
            d->x2 = a1 + 3 * a2;
            //@ close thread2_permissions(d, writing_x);
        }
        {
            do_barrier_2(d); // to writing_y
        }
        m = d->i;
    }
    {
        //@ open thread2_permissions(d, _);
        //@ close thread2_permissions(d, writing_y);
        do_barrier_2(d); // to writing_x
    }
    //@ close thread_run_post(thread2)(d, info);
}