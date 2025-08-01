
// TODO: make this function pass the verification
int to_verify(int* arr)
//@ requires arr[..10] |-> {0, 10, 20, 30, 40, 50, 60, 70, 80, 90};
//@ ensures arr[..10] |-> {0, 10, 20, 31, 40, 50, 60, 70, 80, 90} &*& result == 30;
{
  return arr[3]++;
}

