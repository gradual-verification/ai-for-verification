

// TODO: make this function pass the verification
void increment_all(int* a, int N) 
  //@ requires a[0..N] |-> ?vs &*& forall_(int i; i < 0 || i >= N || (nth(i, vs) < INT_MAX && nth(i, vs) >= INT_MIN));
  //@ ensures a[0..N] |-> ?nvs &*& forall_(int i; i < 0 || i >= length(vs) || nth(i, nvs) == nth(i, vs) + 1);
{
  int k = 0;
  while(k < N)
  {
    a[k] = a[k] + 1;
    k++;
  }
}
