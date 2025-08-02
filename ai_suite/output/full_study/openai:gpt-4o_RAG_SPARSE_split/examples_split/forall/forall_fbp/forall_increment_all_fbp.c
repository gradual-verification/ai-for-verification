#include "limits.h"
#include "stdlib.h"
#include "assert.h"
#include "verifast.h"

// TODO: make this function pass the verification
void increment_all(int* a, int N) 
  //@ requires a[0..N] |-> ?vs &*& forall_(int i; i < 0 || i >= N || (nth(i, vs) < INT_MAX && nth(i, vs) >= INT_MIN));
  //@ ensures a[0..N] |-> ?nvs &*& forall_(int i; i < 0 || i >= length(vs) || nth(i, nvs) == nth(i, vs) + 1);
{
  int k = 0;
  while(k < N)
  //@ invariant 0 <= k &*& k <= N &*& a[0..N] |-> ?vs0 &*& forall_(int i; i < 0 || i >= k || nth(i, vs0) == nth(i, vs) + 1) &*& forall_(int i; i < k || i >= N || (nth(i, vs) < INT_MAX && nth(i, vs) >= INT_MIN));
  {
    //@ open ints(a, N, vs0);
    //@ open ints(a + k, N - k, _);
    //@ nth_map(k, (add)(1), vs);
    //@ nth_map(k, (add)(1), vs0);
    a[k] = a[k] + 1;
    //@ close ints(a + k, N - k, _);
    //@ close ints(a, N, vs0);
    k++;
  }
}