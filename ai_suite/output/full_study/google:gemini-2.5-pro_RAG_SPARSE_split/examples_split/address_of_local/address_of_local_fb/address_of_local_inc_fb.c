#include <limits.h>

void inc(int* i)
  //@ requires *i |-> ?v &*& v < INT_MAX;
  //@ ensures *i |-> v+1;
{
  (*i) = (*i) + 1;
}