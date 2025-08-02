// TODO: make this function pass the verification
void set_to_zero(int* a, int N) 
  //@ requires a[0..N] |-> ?vs;
  //@ ensures a[0..N] |-> ?nvs &*& forall_(int i; i < 0 || i >= length(vs) || nth(i, nvs) == 0);
{
  int k = 0;
  //@ length_nonnegative(vs);
  
  while(k < N) 
    //@ invariant 0 <= k &*& k <= N &*& a[0..k] |-> ?prefix &*& a[k..N] |-> ?suffix &*& forall_(int i; i < 0 || i >= k || nth(i, prefix) == 0);
  {
    //@ open ints(a + k, N - k, suffix);
    a[k] = 0;
    //@ close ints(a + k, 1, cons(0, nil));
    //@ ints_join(a + k);
    k++;
    //@ close forall_(int i; i < 0 || i >= k || nth(i, append(prefix, cons(0, nil))) == 0);
  }
  //@ assert a[0..N] |-> ?nvs;
  //@ assert k == N;
  //@ assert forall_(int i; i < 0 || i >= N || nth(i, nvs) == 0);
  //@ assert forall_(int i; i < 0 || i >= length(vs) || nth(i, nvs) == 0);
}