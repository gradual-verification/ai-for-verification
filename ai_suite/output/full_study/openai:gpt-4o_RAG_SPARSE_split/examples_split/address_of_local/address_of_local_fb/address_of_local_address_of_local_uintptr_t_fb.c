#include <stdint.h>
#include <assert.h>

void inc_uintptr_t(uintptr_t *i)
  //@ requires uintptr(i, ?v);
  //@ ensures uintptr(i, v + 1);
{
  (*i) = (*i) + 1;
}

// TODO: make this function pass the verification
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
      assert(z == 1);
      //@ open pointer(&ptrptr, &ptr);
    }
    //@ open pointer(&ptr, &x);
  }
  //@ open uintptr(&x, 1);
  return;
}