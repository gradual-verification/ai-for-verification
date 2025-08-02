#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>


static int g;
pthread_spinlock_t g_lock;

/*@

predicate g_pred() =
 g |-> ?vf_g
 &*& vf_g >= 0 &*& vf_g <= 1024;

  @*/

/*@

predicate threadfn_info (int *g_l) = true;

inductive quad = quad(int a, int *b, int c, int d);

predicate_family_instance pthread_run_pre(threadfn)
 (void *data, any info) =
     [1/4]g_lock |-> ?lockid
 &*& [1/4]pthread_spinlock(&g_lock, lockid, g_pred)
 &*& info == quad(lockid, &g_lock, lockid, 0)
 &*& true;

predicate_family_instance pthread_run_post(threadfn)
 (void *data, any info) =
     threadfn_info (?g_l)
 &*& [1/4]g_lock |-> ?lockid
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
  //@ assert [1/4]g_lock |-> ?lockid;
  //@ assert [1/4]pthread_spinlock(&g_lock, lockid, g_pred);
  
  pthread_spin_lock(&g_lock);
  //@ assert pthread_spinlock_locked(&g_lock, lockid, g_pred, currentThread, 1/4);
  //@ assert g_pred();
  //@ open g_pred();
  //@ assert g |-> ?vf_g;
  //@ assert vf_g >= 0 && vf_g <= 1024;

  if (g < 1024) { g = g + 1; }
  
  //@ assert g |-> ?new_vf_g;
  //@ assert new_vf_g >= 0 && new_vf_g <= 1024;
  //@ close g_pred();

  pthread_spin_unlock(&g_lock);
  //@ assert [1/4]pthread_spinlock(&g_lock, lockid, g_pred);
  
  //@ close threadfn_info(0);
  //@ close pthread_run_post(threadfn)(_unused, x);
  
  return ((void *) 0);
 }