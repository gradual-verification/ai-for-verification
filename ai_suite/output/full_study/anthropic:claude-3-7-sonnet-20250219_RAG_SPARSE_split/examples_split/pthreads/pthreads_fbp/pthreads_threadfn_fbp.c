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
  //@ assert x == quad(?lockid, &g_lock, lockid, 0);
  
  pthread_spin_lock(&g_lock);
  //@ open g_pred();
  
  if (g < 1024) { g = g + 1; }
  
  //@ close g_pred();
  pthread_spin_unlock(&g_lock);
  
  //@ close threadfn_info(&g);
  //@ close pthread_run_post(threadfn)(_unused, x);
  return ((void *) 0);
}