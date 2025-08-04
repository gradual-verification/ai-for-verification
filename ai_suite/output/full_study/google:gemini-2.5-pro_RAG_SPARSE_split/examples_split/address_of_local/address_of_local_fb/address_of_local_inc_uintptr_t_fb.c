#include <stdint.h>
//@ #include "prelude.h"

// TODO: make this function pass the verification
void inc_uintptr_t(uintptr_t *i)
  //@ requires uintptr(i, ?v);
  //@ ensures uintptr(i, truncate_unsigned(v + 1, sizeof(uintptr_t) * 8));
{
  (*i) = (*i) + 1;
}