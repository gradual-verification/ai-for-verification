#include <stdint.h>
#include <assert.h>

//@ #include "prelude.h"

/***
 * Description:
 * The `inc_uintptr_t` function increments a `uintptr_t` value stored at the given pointer.
 *
 * @param i - A pointer to a `uintptr_t` variable that should be incremented.
 *
 * The function makes sure that the value at i is incremented by 1.
 */
void inc_uintptr_t(uintptr_t *i)
//@ requires uintptr(i, ?v) &*& v < UINTPTR_MAX;
//@ ensures uintptr(i, v + 1);
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