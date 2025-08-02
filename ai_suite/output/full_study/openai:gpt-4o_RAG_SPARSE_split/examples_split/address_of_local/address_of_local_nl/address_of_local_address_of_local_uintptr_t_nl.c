#include <stdint.h>
#include <assert.h>
#include <stdlib.h>

//@ #include "prelude.h"

/***
 * Description:
 * The `inc_uintptr_t` function increments a `uintptr_t` value stored at the given pointer.
 *
 * @param i - A pointer to a `uintptr_t` variable that should be incremented.
 *
 * The function makes sure that the value at i is incremented by 1.
 */
//@ requires uintptr(i, ?v);
//@ ensures uintptr(i, v + 1);
void inc_uintptr_t(uintptr_t *i)
{
  (*i) = (*i) + 1;
}


// TODO: make this function pass the verification
/***
 * Description:
 * The `address_of_local_uintptr_t` function is similar to `address_of_local`
 * but uses `uintptr_t` instead of an integer.
 *
 */
//@ requires true;
//@ ensures true;
void address_of_local_uintptr_t() 
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
  }
  return;
}