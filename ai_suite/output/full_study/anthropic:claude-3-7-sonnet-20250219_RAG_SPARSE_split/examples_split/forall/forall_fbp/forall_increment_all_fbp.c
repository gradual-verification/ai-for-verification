// TODO: make this function pass the verification
void increment_all(int* a, int N) 
  //@ requires a[0..N] |-> ?vs &*& forall_(int i; i < 0 || i >= N || (nth(i, vs) < INT_MAX && nth(i, vs) >= INT_MIN));
  //@ ensures a[0..N] |-> ?nvs &*& forall_(int i; i < 0 || i >= length(vs) || nth(i, nvs) == nth(i, vs) + 1);
{
  int k = 0;
  //@ length_nonnegative(vs);
  
  while(k < N)
    //@ invariant 0 <= k &*& k <= N &*& a[0..N] |-> ?vs_curr &*& forall_(int i; i < 0 || i >= N || (i < k && nth(i, vs_curr) == nth(i, vs) + 1) || (i >= k && nth(i, vs_curr) == nth(i, vs)));
  {
    //@ open ints(a, N, vs_curr);
    //@ assert a[k] |-> ?v_k;
    //@ forall_elim(i, i < 0 || i >= N || (nth(i, vs) < INT_MAX && nth(i, vs) >= INT_MIN), k);
    //@ assert nth(k, vs) < INT_MAX && nth(k, vs) >= INT_MIN;
    a[k] = a[k] + 1;
    //@ close ints(a, k, take(k, vs_curr));
    //@ close ints(a + k + 1, N - k - 1, drop(k + 1, vs_curr));
    //@ assert a[k] |-> nth(k, vs) + 1;
    //@ close ints(a, N, update(k, nth(k, vs) + 1, vs_curr));
    
    //@ assert ints(a, N, ?vs_new);
    //@ assert vs_new == update(k, nth(k, vs) + 1, vs_curr);
    
    /*@
    {
      produce_lemma_function_pointer_chunk forall_update(vs_curr, k, nth(k, vs) + 1)() {
        forall_intro(i);
        if (i < 0 || i >= N) {
        } else if (i < k) {
          forall_elim(i, i < 0 || i >= N || (i < k && nth(i, vs_curr) == nth(i, vs) + 1) || (i >= k && nth(i, vs_curr) == nth(i, vs)), i);
          nth_update(i, k, nth(k, vs) + 1, vs_curr);
        } else if (i == k) {
          nth_update(i, k, nth(k, vs) + 1, vs_curr);
        } else { // i > k
          forall_elim(i, i < 0 || i >= N || (i < k && nth(i, vs_curr) == nth(i, vs) + 1) || (i >= k && nth(i, vs_curr) == nth(i, vs)), i);
          nth_update(i, k, nth(k, vs) + 1, vs_curr);
        }
      };
    }
    @*/
    
    k++;
  }
  
  //@ forall_elim(i, i < 0 || i >= N || (i < k && nth(i, vs_curr) == nth(i, vs) + 1) || (i >= k && nth(i, vs_curr) == nth(i, vs)), 0);
}