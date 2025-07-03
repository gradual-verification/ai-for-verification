#include "stdlib.h"

struct Accumulator {
  int total;
  int count;
};

/*@
predicate Accumulator(struct Accumulator* a, int t, int c) =
  a->total |-> t &*& a->count |-> c &*& malloc_block_Accumulator(a);
@*/

// Verified version of the average function
int average(struct Accumulator* a)
  //@ requires Accumulator(a, ?t, ?c) &*& c > 0;
  //@ ensures Accumulator(a, t, c) &*& result == t / c;
{
  //@ open Accumulator(a, t, c);
  int avg = a->total / a->count;
  //@ div_rem_nonneg(t, c); // Lemma to ensure division properties
  //@ close Accumulator(a, t, c);
  return avg;
}

/* Helper functions to demonstrate usage */

struct Accumulator* create_accumulator(int initial_total, int initial_count)
  //@ requires initial_count >= 0;
  //@ ensures result == 0 ? true : Accumulator(result, initial_total, initial_count);
{
  if (initial_count < 0) return 0;
  struct Accumulator* a = malloc(sizeof(struct Accumulator));
  if (a == 0) return 0;
  a->total = initial_total;
  a->count = initial_count;
  //@ close Accumulator(a, initial_total, initial_count);
  return a;
}

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
  struct Accumulator* acc = create_accumulator(100, 5);
  if (acc == 0) return -1;
  
  int avg = average(acc);
  //@ assert avg == 20;
  
  dispose_accumulator(acc);
  return 0;
}