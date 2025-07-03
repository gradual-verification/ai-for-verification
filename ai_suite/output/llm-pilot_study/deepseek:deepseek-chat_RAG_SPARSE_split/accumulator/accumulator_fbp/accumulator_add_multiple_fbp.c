#include "stdlib.h"

struct Accumulator {
  int total;
  int count;
};

/*@
predicate Accumulator(struct Accumulator* a, int t, int c) =
  a->total |-> t &*& a->count |-> c &*& malloc_block_Accumulator(a);
@*/

// Verified version of add_multiple function
void add_multiple(struct Accumulator* a, int n, int x)
/*@
  requires Accumulator(a, ?t, ?c) 
           &*& n >= 1 &*& x >= 0
           &*& t + n * x <= INT_MAX
           &*& c + n <= INT_MAX;
@*/
/*@
  ensures Accumulator(a, t + n * x, c + n);
@*/
{
  int i = 0;
  /*@
  loop_invariant 0 <= i &*& i <= n;
  loop_invariant Accumulator(a, t + i * x, c + i);
  @*/
  while (i < n)
  {
    a->total += x;
    a->count += 1;
    i++;
  }
}

/*@
lemma void mul_mono(int x, int y)
  requires x <= y &*& 0 <= x &*& 0 <= y;
  ensures x * x <= y * y;
{
  if (x < y) {
    mul_mono(x + 1, y);
  }
}
@*/

// Helper function to create an Accumulator
struct Accumulator* create_accumulator()
//@ requires true;
//@ ensures Accumulator(result, 0, 0);
{
  struct Accumulator* a = malloc(sizeof(struct Accumulator));
  if (a == 0) { abort(); }
  a->total = 0;
  a->count = 0;
  //@ close Accumulator(a, 0, 0);
  return a;
}

// Helper function to dispose an Accumulator
void dispose_accumulator(struct Accumulator* a)
//@ requires Accumulator(a, _, _);
//@ ensures true;
{
  //@ open Accumulator(a, _, _);
  free(a);
}

int main()
//@ requires true;
//@ ensures true;
{
  struct Accumulator* acc = create_accumulator();
  add_multiple(acc, 5, 10);
  dispose_accumulator(acc);
  return 0;
}