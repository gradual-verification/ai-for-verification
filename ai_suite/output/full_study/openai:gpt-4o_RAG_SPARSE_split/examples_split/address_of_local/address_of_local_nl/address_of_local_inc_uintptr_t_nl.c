#include <stdint.h>
#include "prelude.h"

// TODO: make this function pass the verification
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