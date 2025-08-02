#include "stdlib.h"

// the field count keeps track of how many times add/subtract has been called
struct Accumulator {
  int total;
  int count; 
};

/*@
// Define a predicate for the Accumulator structure
predicate Accumulator(struct Accumulator *a; int total, int count) =
    a->total |-> total &*& a->count |-> count &*& malloc_block_Accumulator(a);
@*/

/***
 * Description:
 * The `create` function creates a new accumulator with the given value.
 *
 * @param val: the given value
 *
 * The function makes sure that the created accumulator has total as val and its count as 1. 
 */
struct Accumulator* create(int v)
//@ requires true;
//@ ensures Accumulator(result, v, 1);
{
  struct Accumulator* a = malloc(sizeof(struct Accumulator));
  if (a == 0) {
    abort();
  }
  a->total = v;
  a->count = 1;
  //@ close Accumulator(a, v, 1);
  return a;
}

/***
 * Description:
 * The `add` function adds up the value in the accumulator with a given value. 
 * 
 * @param a: the given accumulator 
 * @param x: the given value
 *
 * The function makes sure the accumulator has the total added by x and the count incremented by 1.
 */
void add(struct Accumulator* a, int x)
//@ requires Accumulator(a, ?t, ?c);
//@ ensures Accumulator(a, t + x, c + 1);
{
  //@ open Accumulator(a, t, c);
  a->total += x;
  a->count += 1;
  //@ close Accumulator(a, t + x, c + 1);
}

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
//@ requires Accumulator(a, ?t, ?c) &*& n >= 0;
//@ ensures Accumulator(a, t + n*x, c + n);
{
  //@ open Accumulator(a, t, c);
  int i = 0;
  //@ int old_t = t;
  //@ int old_c = c;
  while (i < n)
  //@ invariant a->total |-> old_t + i*x &*& a->count |-> old_c + i &*& malloc_block_Accumulator(a) &*& 0 <= i &*& i <= n;
  {
    a->total += x;
    a->count += 1;
    i++;
  }
  //@ close Accumulator(a, old_t + n*x, old_c + n);
}

/***
 * Description:
 * The `subtract` function subtracts the value in the accumulator by a given value. 
 * 
 * @param a: the given accumulator
 * @param x: the given value
 *
 * The function makes sure the accumulator has the total subtracted by x and the count decremented by 1.
 */
void subtract(struct Accumulator* a, int x)
//@ requires Accumulator(a, ?t, ?c);
//@ ensures Accumulator(a, t - x, c + 1);
{
  //@ open Accumulator(a, t, c);
  a->total -= x;
  a->count += 1;
  //@ close Accumulator(a, t - x, c + 1);
}

/***
 * Description:
 * The `reset` function resets the accumulator. 
 * 
 * @param a: the given accumulator
 *
 * The function makes sure the accumulator has the total and count of the accumulator to be 0.
 */
void reset(struct Accumulator* a)
//@ requires Accumulator(a, ?t, ?c);
//@ ensures Accumulator(a, 0, 0);
{
  //@ open Accumulator(a, t, c);
  a->total = 0;
  a->count = 0;
  //@ close Accumulator(a, 0, 0);
}

/***
 * Description:
 * The `average` function returns the average value of each operation. 
 * 
 * @param a: the given accumulator, which has its count > 0
 *
 * The function makes sure the accumulator is not changed, and the return value is total/count of this accumulator.
 */
int average(struct Accumulator* a)
//@ requires Accumulator(a, ?t, ?c) &*& c > 0;
//@ ensures Accumulator(a, t, c) &*& result == t / c;
{
  //@ open Accumulator(a, t, c);
  int avg = a->total / a->count;
  //@ close Accumulator(a, t, c);
  return avg;
}

/***
 * Description:
 * The `destroy` function disposes a given accumulator.
 * 
 * @param a: the given accumulator
 *
 * The function makes sure the accumulator is freed. 
 */
void destroy(struct Accumulator* a)
//@ requires Accumulator(a, ?t, ?c);
//@ ensures emp;
{
  //@ open Accumulator(a, t, c);
  free(a);
}

// TODO: make this function pass the verification
/***
 * Description:
 * The `main` function tests the operations of Accumulator. 
 */
int main() //@ : main
//@ requires true;
//@ ensures true;
{
  struct Accumulator* acc = create(10);
  add(acc, 5);        // total = 15, count = 2
  subtract(acc, 3);   // total = 12, count = 3
  int avg = average(acc); 
  reset(acc);         // total = 0, count = 0
  add_multiple(acc, 2, 8);  // total = 16, count = 2
  destroy(acc);
  return 0;
}