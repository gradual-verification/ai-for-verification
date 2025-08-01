
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
  pthread_spin_lock(&g_lock);

  if (g < 1024) { g = g + 1; }

  pthread_spin_unlock(&g_lock);

  return ((void *) 0);
 }

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

  pthread_spin_init(&g_lock, 0);

  pthread_create(&pthr2, (void *) 0, &threadfn, data);
  pthread_create(&pthr1, (void *) 0, &threadfn, data);

  sleep(600);
  pthread_spin_lock(&g_lock);
  g = 55;
  pthread_spin_unlock(&g_lock);
  sleep(600);

  pthread_join(pthr2, (void *) 0);

  pthread_join(pthr1, (void *) 0);

  pthread_spin_destroy(&g_lock);

  exit(0);
 }


int main (int argc, char** argv) //@ : custom_main_spec
/*@ requires
        module(pthreads_fbp, true) &*& lockset(currentThread, nil);
  @*/
/*@ ensures lockset(currentThread, nil);
  @*/
 {

  run_instance();

  return (0);
 }

