void set_to_zero(int* a, int N) 
  //@ requires a[0..N] |-> ?vs;
  //@ ensures a[0..N] |-> ?nvs &*& forall_(int i; 0 <= i && i < N ==> nth(i, nvs) == 0);
{
  int k = 0;
  while(k < N) 
    //@ invariant a[0..N] |-> ?vs0 &*& 0 <= k &*& k <= N &*& forall_(int i; 0 <= i && i < k ==> nth(i, vs0) == 0);
  {
    a[k] = 0;
    //@ assert a[k] |-> 0;
    //@ assert a[0..k] |-> ?vs1;
    //@ assert a[k+1..N] |-> ?vs2;
    //@ close ints(a, k + 1, append(vs1, cons(0, nil)));
    //@ close ints(a + k + 1, N - k - 1, vs2);
    //@ close ints(a, N, append(append(vs1, cons(0, nil)), vs2));
    k++;
  }
  //@ close ints(a, N, repeat(0, N));
}