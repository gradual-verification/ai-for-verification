#include "prelude.h"

// TODO: make this function pass the verification
void increment_all(int* a, int N)
  //@ requires a[0..N] |-> ?vs;
  //@ ensures a[0..N] |-> ?nvs &*& forall_(int i; i < 0 || i >= length(vs) || nth(i, nvs) == nth(i, vs) + 1);
{
  int k = 0;
  while(k < N)
    /*@
    invariant 0 <= k &*& k <= N &*&
              a[0..N] |-> ?cvs &*& length(cvs) == N &*&
              forall_(int i; i < 0 || i >= k || nth(i, cvs) == nth(i, vs) + 1) &*&
              forall_(int i; i < k || i >= N || nth(i, cvs) == nth(i, vs));
    @*/
  {
    a[k] = a[k] + 1;
    k++;
  }
}