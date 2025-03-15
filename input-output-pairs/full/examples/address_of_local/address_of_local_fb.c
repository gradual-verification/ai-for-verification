#include <stdint.h>
#include <stdbool.h>

void inc(int* i)
  //@ requires integer(i, ?v);
  //@ ensures integer(i, v+1);
{
  (*i) = (*i) + 1;
}

void inc_uintptr_t(uintptr_t *i)
  //@ requires *i |-> ?v;
  //@ ensures *i |-> v + 1;
{
  (*i) = (*i) + 1;
}

void address_of_param(int x) 
  //@ requires true;
  //@ ensures true;
{
    x = 5;
    int* ptr = &x; 
    inc(ptr);
    int z = x;
    assert(z == 6);
}

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

void address_of_local_uintptr_t() 
  //@ requires true;
  //@ ensures true;
{
  uintptr_t x = 0;
  {
    uintptr_t* ptr = &x;
    {
      uintptr_t** ptrptr = &ptr;
      inc_uintptr_t(*ptrptr);
      uintptr_t z = x;
      assert(z == 1);
    }
  }
  return;
  

}



