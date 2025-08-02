// TODO: make this function pass the verification
void array_test1(int* a)
  //@ requires a[0..3] |-> ?vs;
  //@ ensures a[0..3] |-> vs;
{
  //@ open ints_(a, 3, vs);
  int tmp0 = a[0];
  int tmp1 = a[1];
  int tmp2 = a[2];
  //@ close ints_(a, 3, vs);
}