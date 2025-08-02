#include "prelude.h"

// TODO: make this function pass the verification
/***
 * Description:
The set_to_zero function sets 0 to the elements in an array 
of a given length and pointed to by a given pointer.

@param a: the pointer pointing to an array
@param N: the length of the array

It makes sure that the array has its N elements to be 0. 
*/
//@ requires ints(a, N, _);
//@ ensures ints(a, N, repeat(0, N));
void set_to_zero(int* a, int N) 
{
  int k = 0;
  while(k < N) 
  //@ invariant 0 <= k &*& k <= N &*& ints(a, N, ?vs) &*& take(k, vs) == repeat(0, k);
  {
    a[k] = 0;
    //@ assert ints(a + k, N - k, ?vs0);
    //@ ints_to_ints_(a + k);
    //@ ints__split(a + k, 1);
    //@ close ints(a + k, 1, cons(0, nil));
    //@ ints__join(a + k);
    //@ ints__to_ints(a + k);
    //@ ints_join(a);
    k++;
  }
}