#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>


static int g;
pthread_spinlock_t g_lock;

/*@

predicate g_pred() =
 integer(&g, ?vf_g)
 &*& vf_g >= 0 &*& vf_g <= 1024;

@*/

/*@

predicate threadfn_info (int *g_l) = true;

inductive quad = quad(int a, int *b, int c, int d);

predicate_family_instance pthread_run_pre(threadfn)
 (void *data, any info) =
     [1/4]integer(&g_lock, ?lockid)
 &*& [1/4]pthread_spinlock(&g_lock, lockid, g_pred)
 &*& info == quad(lockid, &g_lock, lockid, 0)
 &*& true;

predicate_family_instance pthread_run_post(threadfn)
 (void *data, any info) =
     threadfn_info (?g_l)
 &*& [1/4]integer(&g_lock, ?lockid)
 &*& [1/4]pthread_spinlock(&g_lock, lockid, g_pred)
 &*& info == quad(lockid, &g_lock, lockid, 0)
 &*& true;

@*/


void *threadfn(void* _unused) //@ : pthread_run_joinable
/*@ requires
        pthread_run_pre(threadfn)(_unused, ?x)
    &*& lockset(currentThread, nil);
@*/
/*@ ensures
        pthread_run_post(threadfn)(_unused, x)
    &*& lockset(currentThread, nil)
    &*& result == 0;
@*/
{
    //@ open pthread_run_pre(threadfn)(_unused, x);
    pthread_spin_lock(&g_lock);
    //@ open g_pred();

    if (g < 1024) { g = g + 1; }

    //@ close g_pred();
    pthread_spin_unlock(&g_lock);

    //@ close threadfn_info(0);
    //@ close pthread_run_post(threadfn)(_unused, x);
    return ((void *) 0);
}


// TODO: make this function pass the verification
void run_instance(void)
/*@ requires
        integer(&g, ?vf_g0)
    &*& 0 <= vf_g0 &*& vf_g0 <= 1024
    &*& integer(&g_lock, _)
    &*& lockset(currentThread, nil)
    &*& true;
@*/
/*@ ensures
        integer(&g, _)
    &*& integer(&g_lock, _)
    &*& lockset(currentThread, nil)
    &*& true;
@*/
{
    void *data = (void *) 0;
    pthread_t pthr1, pthr2;

    g = 41;

    //@ close g_pred();
    //@ create_lock_ghost_args(g_pred, nil, nil);
    pthread_spin_init(&g_lock, 0);
    //@ assert pthread_spinlock(&g_lock, ?lockId, g_pred) &*& integer(&g_lock, lockId);

    //@ close pthread_run_pre(threadfn)(data, quad(lockId, &g_lock, lockId, 0));
    pthread_create(&pthr2, (void *) 0, &threadfn, data);

    //@ close pthread_run_pre(threadfn)(data, quad(lockId, &g_lock, lockId, 0));
    pthread_create(&pthr1, (void *) 0, &threadfn, data);

    sleep(600);
    pthread_spin_lock(&g_lock);
    //@ open g_pred();
    
    g = 55;
    
    //@ close g_pred();
    pthread_spin_unlock(&g_lock);
    
    sleep(600);

    pthread_join(pthr2, (void *) 0);
    //@ open pthread_run_post(threadfn)(data, quad(lockId, &g_lock, lockId, 0));
    //@ open threadfn_info(_);

    pthread_join(pthr1, (void *) 0);
    //@ open pthread_run_post(threadfn)(data, quad(lockId, &g_lock, lockId, 0));
    //@ open threadfn_info(_);

    //@ leak integer(&g_lock, _);
    pthread_spin_destroy(&g_lock);
    //@ open g_pred();

    exit(0);
}