void inc(int* i)
  //@ requires *i |-> ?v;
  //@ ensures *i |-> v+1;
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
    //@ close integer(ptr, 0);
    {
      int** ptrptr = &ptr;
      //@ close pointer(ptrptr, ptr);
      inc(*ptrptr);
      //@ open integer(ptr, _);
      int z = x;
      assert(z == 1);
    }
    //@ open pointer(&ptr, _);
  }
  //@ open integer(&x, _);
  return;
}