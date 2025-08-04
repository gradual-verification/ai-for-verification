#include <stdint.h>
#include <limits.h>
//@ #include "prelude.h"

// TODO: make this function pass the verification
void inc_uintptr_t(uintptr_t *i)
  //@ requires *i |-> ?v &*& INT_MIN <= v &*& v < INT_MAX;
  //@ ensures *i |-> v + 1;
{
  //@ if (UINTPTR_MAX < INT_MAX) { assert false; }
  (*i) = (*i) + 1;
}