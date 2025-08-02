#include "stdlib.h"
#include "threading.h"

struct barrier {
    struct mutex *mutex;
    int n;
    int k;
    bool outgoing;
};

//@ predicate barrier(struct barrier *b, int n, int k, bool outgoing) = 
//@     b->mutex |-> ?mutex &*& mutex(mutex, barrier_inv(b)) &*&
//@     b->n |-> n &*& b->k |-> k &*& b->outgoing |-> outgoing;

//@ predicate barrier_inv(struct barrier *b)() = 
//@     b->n |-> ?n &*& b->k |-> ?k &*& b->outgoing |-> ?outgoing &*& 0 <= k &*& k <= n;

void barrier(struct barrier *barrier)
    //@ requires barrier(barrier, ?n, ?k, ?outgoing);
    //@ ensures barrier(barrier, n, 0, false);
{
    struct mutex *mutex = barrier->mutex;
    mutex_acquire(mutex);
    //@ open barrier_inv(barrier)();
    while (barrier->outgoing)
    {
        mutex_release(mutex);
        mutex_acquire(mutex);
        //@ open barrier_inv(barrier)();
    }
    barrier->k++;
    if (barrier->k == barrier->n) {
        barrier->outgoing = true;
        barrier->k--;
        //@ close barrier_inv(barrier)();
        mutex_release(barrier->mutex);
    } else {
        while (!barrier->outgoing)
        {
            mutex_release(mutex);
            mutex_acquire(mutex);
            //@ open barrier_inv(barrier)();
        }
        barrier->k--;
        if (barrier->k == 0) {
            barrier->outgoing = false;
        }
        //@ close barrier_inv(barrier)();
        mutex_release(mutex);
    }
}

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

void thread1(struct data *d)
    //@ requires data(d, ?b, ?x1, ?x2, ?y1, ?y2, ?i) &*& barrier(b, ?n, ?k, ?outgoing);
    //@ ensures data(d, b, _, _, _, _, 0) &*& barrier(b, n, 0, false);
{
    struct barrier *barrier = d->barrier;
    barrier(barrier);
    int N = 0;
    while (N < 30)
    {
        int a1 = d->x1;
        int a2 = d->x2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->y1 = a1 + 2 * a2;
        barrier(barrier);
        a1 = d->y1;
        a2 = d->y2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->x1 = a1 + 2 * a2;
        N = N + 1;
        d->i = N;
        barrier(barrier);
    }
    barrier(barrier);
    d->i = 0;
}