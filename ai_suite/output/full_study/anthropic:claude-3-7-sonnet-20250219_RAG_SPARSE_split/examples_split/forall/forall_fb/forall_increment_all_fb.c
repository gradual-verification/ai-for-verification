// TODO: make this function pass the verification
void increment_all(int* a, int N) 
  //@ requires a[0..N] |-> ?vs;
  //@ ensures a[0..N] |-> ?nvs &*& forall_(int i; i < 0 || i >= length(vs) || nth(i, nvs) == nth(i, vs) + 1);
{
  int k = 0;
  //@ length_nonnegative(vs);
  while(k < N)
    //@ invariant 0 <= k &*& k <= N &*& a[0..k] |-> ?prefix &*& a[k..N] |-> ?suffix &*& length(prefix) == k &*& length(suffix) == N - k &*& append(prefix, suffix) == vs &*& forall_(int i; i < 0 || i >= k || nth(i, prefix) == nth(i, vs) + 1);
  {
    //@ open ints(a + k, N - k, suffix);
    a[k] = a[k] + 1;
    //@ close ints(a + k + 1, N - k - 1, tail(suffix));
    k++;
    //@ assert a[0..k] |-> ?new_prefix;
    //@ assert length(new_prefix) == k;
    //@ assert forall_(int i; i < 0 || i >= k - 1 || nth(i, prefix) == nth(i, vs) + 1);
    //@ assert nth(k-1, new_prefix) == nth(k-1, vs) + 1;
    //@ assert forall_(int i; i < 0 || i >= k || nth(i, new_prefix) == nth(i, vs) + 1);
  }
  //@ assert a[0..N] |-> ?nvs;
  //@ assert forall_(int i; i < 0 || i >= N || nth(i, nvs) == nth(i, vs) + 1);
  //@ assert forall_(int i; i < 0 || i >= length(vs) || nth(i, nvs) == nth(i, vs) + 1);
}