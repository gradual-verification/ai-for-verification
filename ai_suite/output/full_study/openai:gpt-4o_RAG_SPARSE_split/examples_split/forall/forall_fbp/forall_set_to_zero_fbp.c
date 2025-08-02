void set_to_zero(int* a, int N) 
  //@ requires ints(a, N, ?vs);
  //@ ensures ints(a, N, ?nvs) &*& forall_(int i; 0 <= i && i < N ==> nth(i, nvs) == 0);
{
  int k = 0;
  while(k < N) 
    //@ invariant 0 <= k && k <= N &*& ints(a, N, ?vs0) &*& forall_(int i; 0 <= i && i < k ==> nth(i, vs0) == 0);
  {
    //@ open ints(a, N, vs0);
    a[k] = 0;
    //@ close ints(a, N, update(k, 0, vs0));
    k++;
  }
}