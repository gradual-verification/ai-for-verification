#include "prelude.h"

// TODO: make this function pass the verification
/***
 * Description:
 * The `inc` function increments the value stored at the memory location 
 * pointed to by `i`.
 *
 * @param i - A pointer to an integer variable that should be incremented.
 *
 * The function makes sure that the value at i is incremented by 1.
 */
void inc(int* i)
  //@ requires *i |-> ?v;
  //@ ensures *i |-> v + 1;
{
  (*i) = (*i) + 1;
}