#include "stdlib.h"
#include "threading.h"

struct barrier {
    struct mutex *mutex;
    int n;
    int k;
    bool outgoing;
};

//@ predicate barrier(struct barrier *b, int n, int k, bool outgoing) =
//@     b->n |-> n &*& b->k |-> k &*& b->outgoing |-> outgoing &*& b->mutex |-> ?mutex &*& mutex(mutex, barrier_inv(b));

/*@ predicate barrier_inv(struct barrier *b) =
    b->n |-> ?n &*& b->k |-> ?k &*& b->outgoing |-> ?outgoing &*&
    0 <= k &*& k <= n &*&
    (outgoing ? k < n : true);
@*/

struct data {
    struct barrier *barrier;
    int x1;
    int x2;
    int y1;
    int y2;
    int i;
};

//@ predicate data(struct data *d, struct barrier *b, int x1, int x2, int y1, int y2, int i) =
//@     d->barrier |-> b &*& d->x1 |-> x1 &*& d->x2 |-> x2 &*& d->y1 |-> y1 &*& d->y2 |-> y2 &*& d->i |-> i;

struct barrier *create_barrier(int n)
    //@ requires n > 0;
    //@ ensures result != 0 &*& barrier(result, n, 0, false);
{
    struct barrier *barrier = malloc(sizeof(struct barrier));
    if (barrier == 0) abort();
    barrier->n = n;
    barrier->k = 0;
    barrier->outgoing = false;
    //@ close create_mutex_ghost_arg(barrier_inv(barrier));
    struct mutex *mutex = create_mutex();
    barrier->mutex = mutex;
    //@ close barrier(barrier, n, 0, false);
    return barrier;
}

void barrier(struct barrier *barrier)
    //@ requires barrier(barrier, ?n, ?k, ?outgoing);
    //@ ensures barrier(barrier, n, ?k2, ?outgoing2) &*& outgoing2 == false;
{
    struct mutex *mutex = barrier->mutex;
    mutex_acquire(mutex);
    //@ open barrier_inv(barrier);

    while (barrier->outgoing)
    {
        mutex_release(mutex);
        mutex_acquire(mutex);
        //@ open barrier_inv(barrier);
    }

    barrier->k++;
    if (barrier->k == barrier->n) {
        barrier->outgoing = true;
        barrier->k--;
        //@ close barrier_inv(barrier);
        mutex_release(barrier->mutex);
    } else {
        while (!barrier->outgoing)
        {
            mutex_release(mutex);
            mutex_acquire(mutex);
            //@ open barrier_inv(barrier);
        }

        barrier->k--;
        if (barrier->k == 0) {
            barrier->outgoing = false;
        }
        //@ close barrier_inv(barrier);
        mutex_release(mutex);
    }
    //@ close barrier(barrier, n, barrier->k, barrier->outgoing);
}

void barrier_dispose(struct barrier *barrier)
    //@ requires barrier(barrier, ?n, 0, false);
    //@ ensures true;
{
    mutex_dispose(barrier->mutex);
    free(barrier);
}

void thread1(struct data *d)
    //@ requires data(d, ?b, ?x1, ?x2, ?y1, ?y2, ?i) &*& barrier(b, 2, 0, false);
    //@ ensures data(d, b, _, _, _, _, 0) &*& barrier(b, 2, 0, false);
{
    struct barrier *b = d->barrier;
    barrier(b);
    int N = 0;
    while (N < 30)
    {
        int a1 = d->x1;
        int a2 = d->x2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->y1 = a1 + 2 * a2;
        barrier(b);
        a1 = d->y1;
        a2 = d->y2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->x1 = a1 + 2 * a2;
        N = N + 1;
        d->i = N;
        barrier(b);
    }
    barrier(b);
    d->i = 0;
}

void thread2(struct data *d)
    //@ requires data(d, ?b, ?x1, ?x2, ?y1, ?y2, ?i) &*& barrier(b, 2, 0, false);
    //@ ensures data(d, b, _, _, _, _, 0) &*& barrier(b, 2, 0, false);
{
    struct barrier *b = d->barrier;
    barrier(b);
    int m = 0;
    while (m < 30)
    {
        int a1 = d->x1;
        int a2 = d->x2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->y2 = a1 + 3 * a2;
        barrier(b);
        a1 = d->y1;
        a2 = d->y2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->x2 = a1 + 3 * a2;
        barrier(b);
        m = d->i;
    }
    barrier(b);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct data *d = calloc(1, sizeof(struct data));
    if (d == 0) abort();
    
    struct barrier *barrier = create_barrier(2);
    d->barrier = barrier;

    struct thread *t1 = thread_start_joinable(thread1, d);
    struct thread *t2 = thread_start_joinable(thread2, d);
    thread_join(t1);
    thread_join(t2);
   
    barrier_dispose(d->barrier);
    free(d);
    return 0;
}