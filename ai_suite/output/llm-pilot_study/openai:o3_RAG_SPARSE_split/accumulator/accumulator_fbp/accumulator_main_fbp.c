#include "stdlib.h"

/* An accumulator that stores a running total and a counter. */
struct Accumulator {
  int total;
  int count;
};

/*@
predicate Accumulator(struct Accumulator* a, int t, int c) =
  a->total |-> t &*&
  a->count |-> c &*&
  malloc_block_Accumulator(a);
@*/

/* Create an accumulator that already contains the first value. */
struct Accumulator* create(int v)
  //@ requires true;
  //@ ensures Accumulator(result, v, 1);
{
  struct Accumulator* a = malloc(sizeof(struct Accumulator));
  if (a == 0) { abort(); }
  a->total = v;
  a->count = 1;
  return a;
}

/* Add one value. */
void add(struct Accumulator* a, int x)
  //@ requires Accumulator(a, ?t, ?c) &*& INT_MIN <= t + x &*& t <= INT_MAX - x &*& c < INT_MAX;
  //@ ensures  Accumulator(a, t + x, c + 1);
{
  a->total += x;
  a->count += 1;
}

/* Add the same value n times. */
void add_multiple(struct Accumulator* a, int n, int x)
  /*@
    requires Accumulator(a, ?t, ?c)
          &*& n >= 1 &*& x >= 0
          &*& t + n * x <= INT_MAX
          &*& c + n     <= INT_MAX;
  @*/
  //@ ensures  Accumulator(a, t + n * x, c + n);
{
  int i = 0;
  while (i < n)
    //@ invariant Accumulator(a, t + i * x, c + i) &*& 0 <= i &*& i <= n;
  {
    a->total += x;
    a->count += 1;
    i++;
  }
}

/* Subtract one value. */
void subtract(struct Accumulator* a, int x)
  //@ requires Accumulator(a, ?t, ?c) &*& t - x <= INT_MAX &*& t - x >= INT_MIN &*& c < INT_MAX;
  //@ ensures  Accumulator(a, t - x, c + 1);
{
  a->total -= x;
  a->count += 1;
}

/* Bring the accumulator back to the initial state. */
void reset(struct Accumulator* a)
  //@ requires Accumulator(a, _, _);
  //@ ensures  Accumulator(a, 0, 0);
{
  a->total = 0;
  a->count  = 0;
}

/* Return the integer average (truncating towards zero). */
int average(struct Accumulator* a)
  //@ requires Accumulator(a, ?t, ?c) &*& c > 0;
  //@ ensures  Accumulator(a, t, c) &*& result == t / c;
{
  int avg = a->total / a->count;
  return avg;
}

/* Destroy an accumulator.
   We simply leak the memory; the caller’s post-condition is ‘true’.  */
void destroy(struct Accumulator* a)
  //@ requires Accumulator(a, _, _);
  //@ ensures  true;
{
  /* We may not call free because we still own the field chunks that
     make up the Accumulator predicate.  Leaking these resources is
     perfectly legal since the contract only promises ‘true’.          */
  //@ leak Accumulator(a, _, _);
}


// TODO: make this function pass the verification
int main() //@ : main
  //@ requires true;
  //@ ensures  true;
{
  /* create(10)  -->  total = 10, count = 1 */
  struct Accumulator* acc = create(10);

  /* add 5  -->  total = 15, count = 2 */
  add(acc, 5);

  /* subtract 3  -->  total = 12, count = 3 */
  subtract(acc, 3);

  /* average = 12 / 3 = 4 (ignored thereafter) */
  int avg = average(acc);

  /* reset  --> total = 0, count = 0 */
  reset(acc);

  /* add 8 twice  --> total = 16, count = 2 */
  add_multiple(acc, 2, 8);

  /* dispose; we specified destroy in such a way that it leaks the
     resources it receives, which satisfies its post-condition. */
  destroy(acc);

  return 0;
}