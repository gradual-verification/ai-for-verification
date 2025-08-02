void inc_uintptr_t(uintptr_t *i)
  //@ requires *i |-> ?v &*& INT_MIN <= v &*& v < INT_MAX;
  //@ ensures *i |-> v + 1;
{
  (*i) = (*i) + 1;
}


void address_of_local_uintptr_t() 
  //@ requires true;
  //@ ensures true;
{
  uintptr_t x = 0;
  //@ produce_limits(x);
  {
    uintptr_t* ptr = &x;
    //@ assert *ptr |-> 0;
    {
      uintptr_t** ptrptr = &ptr;
      //@ assert *ptrptr |-> ptr &*& *ptr |-> 0;
      inc_uintptr_t(*ptrptr);
      uintptr_t z = x;
      //@ assert z == 1;
      assert(z == 1);
    }
  }
  return;
}