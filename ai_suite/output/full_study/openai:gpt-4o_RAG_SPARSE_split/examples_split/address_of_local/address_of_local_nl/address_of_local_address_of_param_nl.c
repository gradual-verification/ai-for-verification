#include "stdlib.h"
#include "assert.h"

//@ #include "prelude.h"

/***
 * Description:
 * The `inc` function increments the value stored at the memory location 
 * pointed to by `i`.
 *
 * @param i - A pointer to an integer variable that should be incremented.
 *
 * The function makes sure that the value at i is incremented by 1.
 */
//@ requires integer(i, ?v);
//@ ensures integer(i, v + 1);
void inc(int* i)
{
  (*i) = (*i) + 1;
}

// TODO: make this function pass the verification
/***
 * Description:
 * The `address_of_param` function demonstrates passing a local variable’s address.
 *
 * @param x - A local integer variable.
 */
//@ requires true;
//@ ensures true;
void address_of_param(int x) 
{
    x = 5;
    int* ptr = &x; 
    //@ assert integer(ptr, 5);
    inc(ptr);
    int z = x;
    //@ assert z == 6;
    assert(z == 6);
}