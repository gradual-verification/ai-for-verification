#include "stdlib.h"

struct Accumulator {
  int total;
  int count;
};

/*@
predicate Accumulator(struct Accumulator* a, int t, int c) =
  a->total |-> t &*& a->count |-> c &*& malloc_block_Accumulator(a);
@*/

struct Accumulator* create(int v)
  //@ requires emp;
  //@ ensures Accumulator(result, v, 1);
{
  struct Accumulator* a = malloc(sizeof(struct Accumulator));
  if (a == 0) {
    abort();
  }
  a->total = v;
  a->count = 1;
  return a;
}

void add(struct Accumulator* a, int x)
  //@ requires Accumulator(a, ?t, ?c) &*& INT_MIN <= t + x &*& t <= INT_MAX - x &*& c < INT_MAX;
  //@ ensures Accumulator(a, t + x, c + 1);
{
  a->total += x;
  a->count += 1;
}

void subtract(struct Accumulator* a, int x)
  //@ requires Accumulator(a, ?t, ?c) &*& t - x <= INT_MAX &*& t - x >= INT_MIN &*& c < INT_MAX;
  //@ ensures Accumulator(a, t - x, c + 1);
{
  a->total -= x;
  a->count += 1;
}

void reset(struct Accumulator* a)
  //@ requires Accumulator(a, _, _);
  //@ ensures Accumulator(a, 0, 0);
{
  a->total = 0;
  a->count = 0;
}

int current(struct Accumulator* a)
  //@ requires Accumulator(a, ?t, ?c);
  //@ ensures Accumulator(a, t, c) &*& result == t;
{
  int tmp = a->total;
  return tmp;
}

int average(struct Accumulator* a)
  //@ requires Accumulator(a, ?t, ?c) &*& c > 0;
  //@ ensures Accumulator(a, t, c) &*& result == t / c;
{
  int avg = a->total / a->count;
  return avg;
}

void destroy(struct Accumulator* a)
  //@ requires Accumulator(a, _, _);
  //@ ensures emp;
{
  free(a);
}

int main() //@ : main
  //@ requires emp;
  //@ ensures emp;
{
  struct Accumulator* acc = create(10);
  add(acc, 5);
  subtract(acc, 3);
  int avg = average(acc); 
  reset(acc);
  add(acc, 8);
  destroy(acc);
  return 0;
}