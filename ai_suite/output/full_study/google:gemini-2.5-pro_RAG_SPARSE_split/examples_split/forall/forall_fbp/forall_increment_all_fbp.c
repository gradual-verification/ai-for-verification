#include <limits.h>

/*@
#include "list.gh"
#include "listex.gh"
#include "quantifiers.gh"

fixpoint int inc(int x) {
    return x + 1;
}

lemma void forall_map_inc(list<int> vs)
    requires true;
    ensures forall_(int i; i < 0 || i >= length(vs) || nth(i, map(inc, vs)) == nth(i, vs) + 1);
{
    forall__intro( (i) => i < 0 || i >= length(vs) || nth(i, map(inc, vs)) == nth(i, vs) + 1, (i) => {
        if (0 <= i && i < length(vs)) {
            nth_map(i, inc, vs);
        }
    });
}
@*/

// TODO: make this function pass the verification
void increment_all(int* a, int N) 
  //@ requires 0 <= N &*& a[0..N] |-> ?vs &*& forall_(int i; i < 0 || i >= N || (nth(i, vs) < INT_MAX && nth(i, vs) >= INT_MIN));
  //@ ensures a[0..N] |-> ?nvs &*& forall_(int i; i < 0 || i >= length(vs) || nth(i, nvs) == nth(i, vs) + 1);
{
  int k = 0;
  while(k < N)
    /*@
    invariant 0 <= k &*& k <= N &*&
              a[0..k] |-> map(inc, take(k, vs)) &*&
              a[k..N] |-> drop(k, vs);
    @*/
  {
    //@ drop_n_plus_one(k, vs);
    //@ open ints(a + k, N - k, drop(k, vs));
    
    a[k] = a[k] + 1;
    
    //@ ints_join(a);
    
    k++;
  }
  //@ forall_map_inc(vs);
  //@ assert a[0..N] |-> ?nvs;
}