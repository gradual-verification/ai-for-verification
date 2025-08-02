#include "prelude.h"

void increment_all(int* a, int N) 
  //@ requires ints(a, N, ?vs);
  //@ ensures ints(a, N, ?nvs) &*& forall_(int i; i < 0 || i >= length(vs) || nth(i, nvs) == nth(i, vs) + 1);
{
  int k = 0;
  while(k < N)
    //@ invariant 0 <= k &*& k <= N &*& ints(a, N, ?vs0) &*& forall_(int i; i < 0 || i >= k || nth(i, vs0) == nth(i, vs) + 1);
  {
    //@ open ints(a, N, vs0);
    a[k] = a[k] + 1;
    //@ close ints(a, N, update(k, nth(k, vs) + 1, vs0));
    k++;
  }
  //@ close ints(a, N, vs0);
}