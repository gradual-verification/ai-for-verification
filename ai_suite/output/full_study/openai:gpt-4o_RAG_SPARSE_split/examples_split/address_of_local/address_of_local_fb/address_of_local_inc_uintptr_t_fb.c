#include <stdint.h>

// TODO: make this function pass the verification
void inc_uintptr_t(uintptr_t *i)
  //@ requires uintptr(i, ?v);
  //@ ensures uintptr(i, v + 1);
{
  //@ open uintptr(i, v);
  (*i) = (*i) + 1;
  //@ close uintptr(i, v + 1);
}