// TODO: make this function pass the verification
void array_test1(int* a)
  //@ requires a[0..3] |-> ?vs;
  //@ ensures a[0..3] |-> vs;
{
  int tmp0 = a[0];
  int tmp1 = a[1];
  int tmp2 = a[2];
}
// TODO: make this function pass the verification
void array_test1(int* a)
  //@ requires a[0..3] |-> ?vs;
  //@ ensures a[0..3] |-> vs;
{
  //@ open ints(a, 3, vs);
  int tmp0 = a[0];
  //@ assert a[0] |-> tmp0;
  int tmp1 = a[1];
  //@ assert a[1] |-> tmp1;
  int tmp2 = a[2];
  //@ assert a[2] |-> tmp2;
  //@ close ints(a, 3, vs);
}