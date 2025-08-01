

// TODO: make this function pass the verification
void set_to_zero(int* a, int N) 
  //@ requires a[0..N] |-> ?vs;
  //@ ensures a[0..N] |-> ?nvs &*& forall_(int i; i < 0 || i >= length(vs) || nth(i, nvs) == 0);
{
  int k = 0;
  while(k < N) 
  {
    a[k] = 0;
    k++;
  }
}

