void inc(int* i)
  //@ requires integer(i, ?v) &*& INT_MIN <= v &*& v < INT_MAX;
  //@ ensures integer(i, v+1);
{
  (*i) = (*i) + 1;
}

// TODO: make this function pass the verification
void address_of_local() 
  //@ requires true;
  //@ ensures true;
{
  int x = 0;
  //@ close integer(&x, 0);
  {
    int* ptr = &x;
    //@ close pointer(&ptr, &x);
    {
      int** ptrptr = &ptr;
      //@ close pointer(&ptrptr, ptr);
      //@ open pointer(&ptrptr, ptr);
      //@ open pointer(&ptr, &x);
      inc(*ptrptr);
      //@ close pointer(&ptr, &x);
      int z = x;
      assert(z == 1);
    }
    //@ open pointer(&ptr, &x);
  }
  //@ open integer(&x, 1);
  return;
}