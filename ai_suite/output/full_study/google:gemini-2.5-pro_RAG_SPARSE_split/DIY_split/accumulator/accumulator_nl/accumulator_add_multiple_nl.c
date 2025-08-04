#include "stdlib.h"

// the field count keeps track of how many times add/subtract has been called
struct Accumulator {
  int total;
  int count; 
};

/*@
predicate Accumulator(struct Accumulator *a; int total, int count) =
    a->total |-> total &*&
    a->count |-> count &*&
    malloc_block_Accumulator(a);
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `add_multiple` function adds up the value in the accumulator with a given value for multiple times. 
 * 
 * @param a: the given accumulator
 * @param n: the number of times to add
 * @param x: the given value
 *
 * The function makes sure the accumulator has the total added by n*x and the count incremented by n.
 */
void add_multiple(struct Accumulator* a, int n, int x)
    //@ requires Accumulator(a, ?t_old, ?c_old) &*& 0 <= n;
    //@ ensures Accumulator(a, t_old + n * x, c_old + n);
{
  int i = 0;
  while (i < n)
    //@ invariant Accumulator(a, t_old + i * x, c_old + i) &*& 0 <= i &*& i <= n;
  {
    //@ open Accumulator(a, t_old + i * x, c_old + i);
    a->total += x;
    a->count += 1;
    i++;
    //@ close Accumulator(a, t_old + i * x, c_old + i);
  }
}