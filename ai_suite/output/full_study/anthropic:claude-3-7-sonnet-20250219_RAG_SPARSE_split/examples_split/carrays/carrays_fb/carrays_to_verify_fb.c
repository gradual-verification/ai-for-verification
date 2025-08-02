// TODO: make this function pass the verification
int to_verify(int* arr)
//@ requires arr[..10] |-> {0, 10, 20, 30, 40, 50, 60, 70, 80, 90};
//@ ensures arr[..10] |-> {0, 10, 20, 31, 40, 50, 60, 70, 80, 90} &*& result == 30;
{
  //@ open ints(arr, 10, _);
  //@ assert arr[0] |-> 0;
  //@ assert arr[1] |-> 10;
  //@ assert arr[2] |-> 20;
  //@ assert arr[3] |-> 30;
  //@ assert arr[4] |-> 40;
  //@ assert arr[5] |-> 50;
  //@ assert arr[6] |-> 60;
  //@ assert arr[7] |-> 70;
  //@ assert arr[8] |-> 80;
  //@ assert arr[9] |-> 90;
  
  int result = arr[3]++;
  
  //@ assert arr[0] |-> 0;
  //@ assert arr[1] |-> 10;
  //@ assert arr[2] |-> 20;
  //@ assert arr[3] |-> 31;
  //@ assert arr[4] |-> 40;
  //@ assert arr[5] |-> 50;
  //@ assert arr[6] |-> 60;
  //@ assert arr[7] |-> 70;
  //@ assert arr[8] |-> 80;
  //@ assert arr[9] |-> 90;
  //@ close ints(arr, 10, {0, 10, 20, 31, 40, 50, 60, 70, 80, 90});
  
  return result;
}