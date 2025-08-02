#include <stdint.h>
#include <limits.h>

// TODO: make this function pass the verification
void inc_uintptr_t(uintptr_t *i)
  //@ requires *i |-> ?v &*& INT_MIN <= v &*& v < INT_MAX;
  //@ ensures *i |-> v + 1;
{
  //@ integer__limits(i);
  (*i) = (*i) + 1;
}