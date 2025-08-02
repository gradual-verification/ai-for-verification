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
  //@ int* px = &x;
  //@ close px |-> 0;
  {
    int* ptr = &x;
    //@ assert ptr == px;
    {
      int** ptrptr = &ptr;
      //@ close *ptrptr |-> px;
      inc(*ptrptr);
      int z = x;
      //@ open px |-> z;
      assert(z == 1);
      //@ close px |-> z;
    }
    //@ open *ptrptr |-> px;
  }
  //@ open px |-> _;
  return;
}