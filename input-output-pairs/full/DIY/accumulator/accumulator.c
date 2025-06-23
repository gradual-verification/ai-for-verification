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

void add(struct Accumulator* a, int x)
  //@ requires Accumulator(a, ?t, ?c) &*& INT_MIN <= t + x &*& t <= INT_MAX - x &*& c < INT_MAX;
  //@ ensures Accumulator(a, t + x, c + 1);
{
  //@ open Accumulator(a, t, c);
  a->total += x;
  a->count += 1;
  //@ close Accumulator(a, t + x, c + 1);
}

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
  while (i < n)
    /*@ invariant Accumulator(a, t + i * x, c + i) 
                 &*& i <= n;
    @*/
  {
    //@ open Accumulator(a, t + i * x, c + i);
    //@ mul_mono_l(i + 1, n, x);
    a->total += x;
    a->count += 1;
    i++;
    //@ close Accumulator(a, t + i * x, c + i);
  }
}

void subtract(struct Accumulator* a, int x)
  //@ requires Accumulator(a, ?t, ?c) &*& t - x <= INT_MAX &*& t - x >= INT_MIN &*& c < INT_MAX;
  //@ ensures Accumulator(a, t - x, c + 1);
{
  //@ open Accumulator(a, t, c);
  a->total -= x;
  a->count += 1;
  //@ close Accumulator(a, t - x, c + 1);
}

void reset(struct Accumulator* a)
  //@ requires Accumulator(a, _, _);
  //@ ensures Accumulator(a, 0, 0);
{
  //@ open Accumulator(a, _, _);
  a->total = 0;
  a->count = 0;
  //@ close Accumulator(a, 0, 0);
}

int current(struct Accumulator* a)
  //@ requires Accumulator(a, ?t, ?c);
  //@ ensures Accumulator(a, t, c) &*& result == t;
{
  //@ open Accumulator(a, t, c);
  int tmp = a->total;
  //@ close Accumulator(a, t, c);
  return tmp;
}

int average(struct Accumulator* a)
  //@ requires Accumulator(a, ?t, ?c) &*& c > 0;
  //@ ensures Accumulator(a, t, c) &*& result == t / c;
{
  //@ open Accumulator(a, t, c);
  int avg = a->total / a->count;
  //@ close Accumulator(a, t, c);
  return avg;
}

void destroy(struct Accumulator* a)
  //@ requires Accumulator(a, _, _);
  //@ ensures true;
{
  //@ open Accumulator(a, _, _);
  free(a);
}

int main() //@ : main
  //@ requires true;
  //@ ensures true;
{
  struct Accumulator* acc = create(10);
  add(acc, 5);        // total = 15, count = 2
  subtract(acc, 3);   // total = 12, count = 3
  int avg = average(acc); 
  //@ assert avg == 4;
  reset(acc);         // total = 0, count = 0
  add_multiple(acc, 2, 8);  // total = 16, count = 2
  destroy(acc);
  return 0;
}