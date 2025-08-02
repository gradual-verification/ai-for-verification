#include <stdint.h>
#include <limits.h>

// Function to increment a uintptr_t value
void inc_uintptr_t(uintptr_t *i)
  //@ requires *i |-> ?v &*& INT_MIN <= v &*& v < INT_MAX;
  //@ ensures *i |-> v + 1;
{
  (*i) = (*i) + 1;
}

// Function to demonstrate the use of address of local uintptr_t
void address_of_local_uintptr_t() 
  //@ requires true;
  //@ ensures true;
{
  uintptr_t x = 0;
  //@ close uintptr(&x, 0);
  {
    uintptr_t* ptr = &x;
    //@ close pointer(&ptr, &x);
    {
      uintptr_t** ptrptr = &ptr;
      //@ close pointer(&ptrptr, &ptr);
      inc_uintptr_t(*ptrptr);
      uintptr_t z = x;
      //@ open uintptr(&x, 1);
      assert(z == 1);
    }
    //@ open pointer(&ptr, &x);
  }
  //@ open uintptr(&x, 1);
  return;
}