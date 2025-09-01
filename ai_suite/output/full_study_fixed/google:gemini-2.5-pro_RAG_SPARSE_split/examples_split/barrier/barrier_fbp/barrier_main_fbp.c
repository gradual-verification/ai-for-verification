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

predicate_family_instance thread_run_pre(thread2)(struct data *d, any info) =
    [1/2]d->phase2 |-> writing_x &*& [1/2]d->inside2 |-> false &*& [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x2 |-> ?_ &*&
    [1/3]d->barrier |-> ?barrier &*& [1/2]barrier(barrier, 2, my_barrier_inv(d));

predicate_family_instance thread_run_post(thread2)(struct data *d, any info) =
    [1/2]d->phase2 |-> writing_x &*& [1/2]d->inside2 |-> false &*& [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x2 |-> ?_ &*&
    [1/3]d->barrier |-> ?barrier &*& [1/2]barrier(barrier, 2, my_barrier_inv(d));

@*/


struct barrier *create_barrier(int n)
    //@ requires 2 <= n &*& create_barrier_ghost_arg(?inv);
    //@ ensures barrier(result, n, inv);
{
    struct barrier *barrier = malloc(sizeof(struct barrier));
    if (barrier == 0) abort();
    barrier->n = n;
    barrier->k = 0;
    barrier->outgoing = false;
    //@ close barrier_inv(barrier, n, inv)();
    //@ close create_mutex_ghost_arg(barrier_inv(barrier, n, inv));
    struct mutex *mutex = create_mutex();
    barrier->mutex = mutex;
    //@ open create_barrier_ghost_arg(inv);
    return barrier;
}


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

    {
        while (barrier->outgoing)
        //@ invariant barrier->k |-> ?k &*& barrier->outgoing |-> ?outgoing &*& inv(k, outgoing) &*& outgoing ? 1 <= k &*& k < n : 0 <= k &*& k < n;
        {
            //@ close barrier_inv(barrier, n, inv)();
            mutex_release(mutex);
            mutex_acquire(mutex);
            //@ open barrier_inv(barrier, n, inv)();
        }
    }
    //@ open inv(?k_old, false);
    //@ call_barrier_enter(enter, k_old);
    barrier->k++;
    //@ close inv(barrier->k, false);
    if (barrier->k == barrier->n) {
        barrier->outgoing = true;
        barrier->k--;
        //@ open inv(barrier->k + 1, false);
        //@ close inv(barrier->k, true);
        //@ close barrier_inv(barrier, n, inv)();
        mutex_release(barrier->mutex);
    } else {
        while (!barrier->outgoing)
        //@ invariant barrier->k |-> ?k &*& barrier->outgoing |-> ?outgoing &*& inv(k, outgoing) &*& outgoing ? 1 <= k &*& k < n : 0 <= k &*& k < n;
        {
            //@ close barrier_inv(barrier, n, inv)();
            mutex_release(mutex);
            mutex_acquire(mutex);
            //@ open barrier_inv(barrier, n, inv)();
        }
        //@ open inv(?k_inside, true);
        //@ call_barrier_exit(exit, k_inside);
        barrier->k--;
        if (barrier->k == 0) {
            barrier->outgoing = false;
        }
        //@ close inv(barrier->k, barrier->outgoing);
        //@ close barrier_inv(barrier, n, inv)();
        mutex_release(mutex);
    }
    //@ close barrier_exiting(exit)(n, inv);
}


void barrier_dispose(struct barrier *barrier)
    //@ requires barrier(barrier, ?n, ?inv);
    //@ ensures inv(_, _);
{
    //@ open barrier(barrier, n, inv);
    mutex_dispose(barrier->mutex);
    //@ open barrier_inv(barrier, n, inv)();
    free(barrier);
}


void thread1(struct data *d) //@ : thread_run_joinable
    //@ requires thread_run_pre(thread1)(d, ?info);
    //@ ensures thread_run_post(thread1)(d, info);
{
    //@ open thread_run_pre(thread1)(d, info);
    struct barrier *b = d->barrier;
    {
        /*@
        predicate P(int k, bool outgoing) =
            [1/2]d->phase1 |-> ?p1 &*& [1/2]d->inside1 |-> ?i1 &*&
            (i1 ? true : [1/2]d->y1 |-> _ &*& [1/2]d->y2 |-> _ &*& d->x1 |-> _ &*& d->i |-> _) &*&
            my_barrier_inv(d)(k, outgoing);
        lemma void enter_lemma(int k) : barrier_enter
            requires barrier_incoming(this)(2, P, ?exit) &*& P(k, false) &*& 0 <= k &*& k < 2;
            ensures k == 1 ? barrier_exiting(exit)(2, P) &*& P(k, true) : barrier_inside(exit)(2, P) &*& P(k + 1, false);
        {
            open P(k, false);
            open my_barrier_inv(d)(k, false);
            d->inside1 = true;
            close my_barrier_inv(d)(k + 1, false);
            close P(k + 1, false);
        }
        lemma void exit_lemma(int k) : barrier_exit
            requires barrier_inside(this)(2, P) &*& P(k, true) &*& 1 <= k &*& k < 2;
            ensures barrier_exiting(this)(2, P) &*& (k == 1 ? P(0, false) : P(k - 1, true));
        {
            open P(k, true);
            open my_barrier_inv(d)(k, true);
            d->inside1 = false;
            close my_barrier_inv(d)(k - 1, false);
            close P(k - 1, false);
        }
        @*/
        //@ produce_lemma_function_pointer_chunk(enter_lemma);
        //@ produce_lemma_function_pointer_chunk(exit_lemma);
        //@ close P(0, false);
        barrier(b);
        //@ open P(_, _);
    }
    int N = 0;
    while (N < 30)
      //@ invariant true; // Loop verification is out of scope for this task.
    {
        int a1 = d->x1;
        int a2 = d->x2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->y1 = a1 + 2 * a2;
        {
            
            barrier(b);
           
        }
        a1 = d->y1;
        a2 = d->y2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->x1 = a1 + 2 * a2;
        N = N + 1;
        d->i = N;
        {
            
            barrier(b);

        }
    }
    {
        
        barrier(b);

    }
    d->i = 0;
    //@ close thread_run_post(thread1)(d, info);
}


void thread2(struct data *d) //@ : thread_run_joinable
    //@ requires thread_run_pre(thread2)(d, ?info);
    //@ ensures thread_run_post(thread2)(d, info);
{
    //@ open thread_run_pre(thread2)(d, info);
    struct barrier *b = d->barrier;
    {
        
        barrier(b);
        
    }
    int m = 0;
    while (m < 30)
        //@ invariant true; // Loop verification is out of scope for this task.
    {
        int a1 = d->x1;
        int a2 = d->x2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->y2 = a1 + 3 * a2;
        {
            
            barrier(b);
           
        }
        a1 = d->y1;
        a2 = d->y2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->x2 = a1 + 3 * a2;
        {
           
            barrier(b);
          
        }
        m = d->i;
    }
    {
        
        barrier(b);
       
    }
    //@ close thread_run_post(thread2)(d, info);
}


// TODO: make this function pass the verification
int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct data *d = calloc(1, sizeof(struct data));
    if (d == 0) abort();
    //@ open data(d, _, _, _, _, _, _, _, _, _, _, _);
    
    d->phase = writing_x;
    d->phase1 = writing_x;
    d->phase2 = writing_x;
    d->inside1 = false;
    d->inside2 = false;
    
    //@ close data_phase(d, writing_x);
    //@ close [1/2]data_phase1(d, writing_x);
    //@ close [1/2]data_phase2(d, writing_x);
    //@ close [1/2]data_inside1(d, false);
    //@ close [1/2]data_inside2(d, false);
    //@ close my_barrier_inv(d)(0, false);
    //@ close create_barrier_ghost_arg(my_barrier_inv(d));
    struct barrier *b = create_barrier(2);
    d->barrier = b;

    //@ close [1/2]data_y1(d, 0);
    //@ close [1/2]data_y2(d, 0);
    //@ close data_x1(d, 0);
    //@ close data_i(d, 0);
    //@ close [1/3]data_barrier(d, b);
    //@ close [1/2]barrier(b, 2, my_barrier_inv(d));
    //@ close thread_run_pre(thread1)(d, unit);
    struct thread *t1 = thread_start_joinable(thread1, d);

    //@ close [1/2]data_y1(d, 0);
    //@ close [1/2]data_y2(d, 0);
    //@ close data_x2(d, 0);
    //@ close [1/3]data_barrier(d, b);
    //@ close [1/2]barrier(b, 2, my_barrier_inv(d));
    //@ close thread_run_pre(thread2)(d, unit);
    struct thread *t2 = thread_start_joinable(thread2, d);
    
    thread_join(t1);
    //@ open thread_run_post(thread1)(d, unit);
    
    thread_join(t2);
    //@ open thread_run_post(thread2)(d, unit);
   
    barrier_dispose(d->barrier);
    //@ open my_barrier_inv(d)(?k, ?outgoing);
    //@ assert k == 0 && outgoing == false;
  
    //@ close data(d, b, writing_x, writing_x, writing_x, false, false, _, _, _, _, 0);
    
    free(d);
    return 0;
}