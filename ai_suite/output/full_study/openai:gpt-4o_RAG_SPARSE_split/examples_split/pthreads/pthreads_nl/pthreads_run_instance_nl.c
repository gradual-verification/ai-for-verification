#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>

//@ #include "prelude.h"

//@ predicate g_lock_inv() = integer(&g, ?value) &*& 0 <= value &*& value <= 1024;

static int g;
pthread_spinlock_t g_lock;

/*@
predicate_family_instance pthread_run_pre(threadfn)(void *data, any info) =
    integer(&g, ?value) &*& 0 <= value &*& value <= 1024 &*&
    pthread_spinlock(&g_lock, ?lockId, g_lock_inv) &*&
    lockset(currentThread, nil);

predicate_family_instance pthread_run_post(threadfn)(void *data, any info) =
    integer(&g, ?value) &*& 0 <= value &*& value <= 1024 &*&
    pthread_spinlock(&g_lock, ?lockId, g_lock_inv) &*&
    lockset(currentThread, nil);
@*/

void *threadfn(void* _unused)
{
    //@ open pthread_run_pre(threadfn)(_unused, _);
    pthread_spin_lock(&g_lock);
    //@ open g_lock_inv();
    if (g < 1024) { g = g + 1; }
    //@ close g_lock_inv();
    pthread_spin_unlock(&g_lock);
    //@ close pthread_run_post(threadfn)(_unused, _);
    return ((void *) 0);
}

/*@
predicate_family_instance pthread_run_pre(run_instance)(void *data, any info) =
    integer(&g, ?value) &*& 0 <= value &*& value <= 1024 &*&
    pthread_spinlock(&g_lock, ?lockId, g_lock_inv) &*&
    lockset(currentThread, nil);

predicate_family_instance pthread_run_post(run_instance)(void *data, any info) =
    integer(&g, ?value) &*& 0 <= value &*& value <= 1024 &*&
    pthread_spinlock(&g_lock, ?lockId, g_lock_inv) &*&
    lockset(currentThread, nil);
@*/

void run_instance(void)
{
    //@ open pthread_run_pre(run_instance)(0, _);
    void *data = (void *) 0;
    pthread_t pthr1, pthr2;

    g = 41;
    //@ close g_lock_inv();
    pthread_spin_init(&g_lock, 0);

    //@ close pthread_run_pre(threadfn)(data, _);
    pthread_create(&pthr2, (void *) 0, &threadfn, data);
    //@ close pthread_run_pre(threadfn)(data, _);
    pthread_create(&pthr1, (void *) 0, &threadfn, data);

    sleep(600);
    pthread_spin_lock(&g_lock);
    //@ open g_lock_inv();
    g = 55;
    //@ close g_lock_inv();
    pthread_spin_unlock(&g_lock);
    sleep(600);

    pthread_join(pthr2, (void *) 0);
    //@ open pthread_run_post(threadfn)(data, _);

    pthread_join(pthr1, (void *) 0);
    //@ open pthread_run_post(threadfn)(data, _);

    pthread_spin_destroy(&g_lock);
    //@ close pthread_run_post(run_instance)(0, _);

    exit(0);
}