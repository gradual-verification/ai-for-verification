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

predicate_ctor my_barrier_inv(struct data *d; int k, bool exiting) =
    d->phase |-> ?p &*&
    [1/2]d->inside1 |-> ?i1 &*&
    [1/2]d->inside2 |-> ?i2 &*&
    [1/2]d->phase1 |-> ?p1 &*& p == (exiting && i1 ? next_phase(p1) : p1) &*&
    [1/2]d->phase2 |-> ?p2 &*& p == (exiting && i2 ? next_phase(p2) : p2) &*&
    k == (i1 ? 1 : 0) + (i2 ? 1 : 0) - (exiting ? 1 : 0) &*&
    switch (p) {
        case writing_x: return
            (i1 ? [1/2]d->y1 |-> ?y1v &*& [1/2]d->y2 |-> ?y2v &*& d->x1 |-> ?x1v &*& d->i |-> _ &*& 0 <= y1v &*& y1v <= 1000 &*& 0 <= y2v &*& y2v <= 1000 : true) &*&
            (i2 ? [1/2]d->y1 |-> ?y1v &*& [1/2]d->y2 |-> ?y2v &*& d->x2 |-> ?x2v &*& 0 <= y1v &*& y1v <= 1000 &*& 0 <= y2v &*& y2v <= 1000 : true);
        case writing_y: return
            (i1 ? [1/2]d->x1 |-> ?x1v &*& [1/2]d->x2 |-> ?x2v &*& d->y1 |-> ?y1v &*& 0 <= x1v &*& x1v <= 1000 &*& 0 <= x2v &*& x2v <= 1000 : true) &*&
            (i2 ? [1/2]d->x1 |-> ?x1v &*& [1/2]d->x2 |-> ?x2v &*& d->y2 |-> ?y2v &*& d->i |-> _ &*& 0 <= x1v &*& x1v <= 1000 &*& 0 <= x2v &*& x2v <= 1000 : true);
    };

@*/


/*@

predicate_family_instance thread_run_pre(thread2)(struct data *d, any info) =
    [1/2]d->phase2 |-> writing_x &*& [1/2]d->inside2 |-> false &*&
    [1/2]d->y1 |-> 0 &*& [1/2]d->y2 |-> 0 &*& d->x2 |-> 0 &*&
    [1/3]d->barrier |-> ?barrier &*& [1/2]barrier(barrier, 2, my_barrier_inv(d));

predicate_family_instance thread_run_post(thread2)(struct data *d, any info) =
    [1/2]d->phase2 |-> writing_x &*& [1/2]d->inside2 |-> false &*&
    [1/2]d->y1 |-> _ &*& [1/2]d->y2 |-> _ &*& d->x2 |-> _ &*&
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
lemma void thread2_barrier(struct data *d)
    requires
        [1/3]d->barrier |-> ?b &*& [1/2]barrier(b, 2, my_barrier_inv(d)) &*&
        [1/2]d->phase2 |-> ?p2 &*&
        [1/2]d->inside2 |-> false &*&
        (p2 == writing_x ?
            [1/2]d->y1 |-> ?y1v &*& [1/2]d->y2 |-> ?y2v &*& d->x2 |-> ?x2v &*& 0 <= y1v &*& y1v <= 1000 &*& 0 <= y2v &*& y2v <= 1000
        :
            [1/2]d->x1 |-> ?x1v &*& [1/2]d->x2 |-> ?x2v &*& d->y2 |-> ?y2v &*& d->i |-> _ &*& 0 <= x1v &*& x1v <= 1000 &*& 0 <= x2v &*& x2v <= 1000
        );
    ensures
        [1/3]d->barrier |-> b &*& [1/2]barrier(b, 2, my_barrier_inv(d)) &*&
        [1/2]d->phase2 |-> next_phase(p2) &*&
        [1/2]d->inside2 |-> false &*&
        (next_phase(p2) == writing_x ?
            [1/2]d->y1 |-> ?y1v &*& [1/2]d->y2 |-> ?y2v &*& d->x2 |-> ?x2v &*& 0 <= y1v &*& y1v <= 1000 &*& 0 <= y2v &*& y2v <= 1000
        :
            [1/2]d->x1 |-> ?x1v &*& [1/2]d->x2 |-> ?x2v &*& d->y2 |-> ?y2v &*& d->i |-> _ &*& 0 <= x1v &*& x1v <= 1000 &*& 0 <= x2v &*& x2v <= 1000
        );
{
    open barrier(b, 2, my_barrier_inv(d));
    struct mutex *mutex = b->mutex;

    mutex_acquire(mutex);
    open barrier_inv(b, 2, my_barrier_inv(d))();

    while (b->outgoing)
        invariant b->mutex |-> mutex &*& b->n |-> 2 &*& [1/2]mutex(mutex, barrier_inv(b, 2, my_barrier_inv(d))) &*&
                  [1/2]d->phase2 |-> p2 &*& [1/2]d->inside2 |-> false &*&
                  (p2 == writing_x ?
                      [1/2]d->y1 |-> ?y1v &*& [1/2]d->y2 |-> ?y2v &*& d->x2 |-> ?x2v &*& 0 <= y1v &*& y1v <= 1000 &*& 0 <= y2v &*& y2v <= 1000
                  :
                      [1/2]d->x1 |-> ?x1v &*& [1/2]d->x2 |-> ?x2v &*& d->y2 |-> ?y2v &*& d->i |-> _ &*& 0 <= x1v &*& x1v <= 1000 &*& 0 <= x2v &*& x2v <= 1000
                  );
    {
        close barrier_inv(b, 2, my_barrier_inv(d))();
        mutex_release(mutex);
        mutex_acquire(mutex);
        open barrier_inv(b, 2, my_barrier_inv(d))();
    }
    assert b->outgoing |-> false;

    open my_barrier_inv(d)(?k_old, false);
    d->inside2 = true;
    b->k++;
    int k_new = b->k;
    
    switch(p2) {
        case writing_x:
            close my_barrier_inv(d)(k_new, false);
            break;
        case writing_y:
            close my_barrier_inv(d)(k_new, false);
            break;
    }

    if (k_new == 2) {
        b->outgoing = true;
        b->k--;
        open my_barrier_inv(d)(2, false);
        d->phase = next_phase(d->phase);
        d->inside2 = false;
        close my_barrier_inv(d)(1, true);
        close barrier_inv(b, 2, my_barrier_inv(d))();
        mutex_release(mutex);
    } else {
        close barrier_inv(b, 2, my_barrier_inv(d))();
        mutex_release(mutex);
        mutex_acquire(mutex);
        open barrier_inv(b, 2, my_barrier_inv(d))();
        while (!b->outgoing)
            invariant b->mutex |-> mutex &*& b->n |-> 2 &*& [1/2]mutex(mutex, barrier_inv(b, 2, my_barrier_inv(d)));
        {
            close barrier_inv(b, 2, my_barrier_inv(d))();
            mutex_release(mutex);
            mutex_acquire(mutex);
            open barrier_inv(b, 2, my_barrier_inv(d))();
        }
        assert b->outgoing |-> true;
        open my_barrier_inv(d)(?k_exit, true);
        b->k--;
        d->inside2 = false;
        if (b->k == 0) {
            b->outgoing = false;
            close my_barrier_inv(d)(0, false);
        } else {
            close my_barrier_inv(d)(b->k, true);
        }
        close barrier_inv(b, 2, my_barrier_inv(d))();
        mutex_release(mutex);
    }
    
    d->phase2 = next_phase(p2);
    close barrier(b, 2, my_barrier_inv(d));
}
@*/

void thread2(struct data *d) //@ : thread_run_joinable
    //@ requires thread_run_pre(thread2)(d, ?info);
    //@ ensures thread_run_post(thread2)(d, info);
{
    open thread_run_pre(thread2)(d, info);
    
    thread2_barrier(d);
    
    int m = 0;
    while (m < 30)
        /*@
        invariant
            [1/3]d->barrier |-> ?b &*& [1/2]barrier(b, 2, my_barrier_inv(d)) &*&
            [1/2]d->inside2 |-> false &*&
            [1/2]d->phase2 |-> writing_y &*&
            [1/2]d->x1 |-> ?x1v &*& [1/2]d->x2 |-> ?x2v &*& d->y2 |-> ?y2v &*& d->i |-> ?iv &*&
            0 <= x1v &*& x1v <= 1000 &*& 0 <= x2v &*& x2v <= 1000;
        @*/
    {
        int a1 = d->x1;
        int a2 = d->x2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->y2 = a1 + 3 * a2;
        
        thread2_barrier(d);
        
        a1 = d->y1;
        a2 = d->y2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->x2 = a1 + 3 * a2;
        
        thread2_barrier(d);
        
        m = d->i;
    }
    
    thread2_barrier(d);
    
    close thread_run_post(thread2)(d, info);
}