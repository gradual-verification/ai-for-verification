
// TODO: make this function pass the verification
void array_test2(int* a)
  //@ requires a[..?n] |-> ?vs &*& 1 < n;
  //@ ensures a[..n] |-> update(0, 10, vs);
{
  int a1_old = a[1];
  a[0] = 10;
  int tmp = a[0];
  assert(tmp == 10);
  int a1 = a[1];
  assert(a1_old == a1);
}

