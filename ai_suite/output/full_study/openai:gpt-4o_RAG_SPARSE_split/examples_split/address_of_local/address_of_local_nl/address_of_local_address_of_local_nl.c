#include "prelude.h"

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
    //@ requires integer(i, ?v);
    //@ ensures integer(i, v + 1);
{
  (*i) = (*i) + 1;
}

// TODO: make this function pass the verification
/***
 * Description:
 * The `address_of_local` function demonstrates the use of pointers 
 * and pointer-to-pointer relationships.
 *
 */
void address_of_local() 
    //@ requires true;
    //@ ensures true;
{
  int x = 0;
  //@ integer_limits(&x);
  {
    int* ptr = &x;
    //@ integer_limits(ptr);
    {
      int** ptrptr = &ptr;
      //@ pointer_limits(ptrptr);
      inc(*ptrptr);
      int z = x;
      assert(z == 1);
    }
  }
  return;
}