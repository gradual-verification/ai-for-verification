

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
  {
    int* ptr = &x;
    {
      int** ptrptr = &ptr;
      inc(*ptrptr);
      int z = x;
      assert(z == 1);
    }
  }
  return;
  

}

